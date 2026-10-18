# S5-MODEL-STEP — channel-level `update_add_htlc` transition (MODEL-02 / LN-CH-101)

- **Lane:** `S5-MODEL-STEP`
- **Obligations:** `MODEL-02`, `LN-CH-101`
- **Status:** complete (additive relation + proofs); no shared file needed changing.
- **Owned files changed:**
  - `LnLean/Channel/State.lean` — 228 lines added, 0 deleted (append-only layer; `Step` and `ProtocolEvent` untouched).
  - `LnLean/Proofs/Channel/StateTransitionTargets.lean` — new, 736 lines.
  - `agents/reports/swarm5/S5-MODEL-STEP.md` — this report.
- **Blockers:** none for the owned scope. The literal `Step.update_add_htlc` *constructor* requested by `MODEL-02` is blocked by forbidden lifecycle-only files; the exact migration list is in §5.

---

## 1. Result

`MODEL-02` reports that `Step` has no `update_add_htlc` constructor and that
affordability only exists on E37's successor functions.  This lane closes the
model gap **additively**:

1. `LnLean.Channel.UpdateStep hashFn` is a new transition relation over the
   existing `Channel` record.  It embeds the unchanged lifecycle relation
   (`UpdateStep.lifecycle : Step c e c' → UpdateStep hashFn c (.lifecycle e) c'`)
   and adds BOLT 2 `update_add_htlc`, `update_fulfill_htlc`, and
   `update_fail_htlc`.
2. `AffordableAdd` is the constructor guard for the add: positive amount,
   `cltv_expiry` bound, receiver `htlc_minimum_msat`, offering-balance
   coverage, reserve, and receiver `max_htlc_value_in_flight_msat`.
3. `UpdateStep` is proved to preserve E37's ledger equation and
   `ReserveInvariant`; the local add target is *definitionally* E37's
   `committedAdd`, and `AffordableAdd` implies E37's
   `AffordableCommittedAdd`.
4. The existing E37 counterexample survives: without the affordability guard
   the ledger equation is still false, so the guard is not vacuous.

No existing transition, theorem, counterexample, or dependency was removed or
weakened.

### Why not a `Step` constructor

`Step` is lifecycle-only in the rest of the tree.  Adding a balance/HTLC-moving
constructor to `Step` would require a new `ProtocolEvent` constructor and would
break at least the following owned-elsewhere results:

| File | Declaration | Failure mode |
|---|---|---|
| `LnLean/Proofs/Liveness.lean` | `step?`, `step?_sound`, `step?_complete` | exhaustive `match` on `ProtocolEvent`; new event has no executable branch |
| `LnLean/Proofs/Payment/LiquidityProps.lean` | `step_preserves_balance` | a changing `Step` falsifies the statement |
| `LnLean/Proofs/ModelHardening/F03.lean` | `step_htlcs_eq`, `step_preserves_ledgerBalanced` | HTLC list no longer invariant |
| `LnLean/Proofs/WaveD/D14.lean` | `waveD_d14_step_balance`, `waveD_d14_step_htlcs` | counter-model relies on `Step` not changing balances/HTLCs |
| `LnLean/Proofs/PhaseC2/LivenessDelivery.lean` | `step_htlcs_eq` | HTLC list no longer invariant |
| `LnLean/Proofs/Channel/StateMachineProps.lean` | `step_allowedPhaseTransition` | explicit `cases h with` has no `update_add_htlc` branch |
| `LnLean/Channel/Laws.lean`, `LnLean/Proofs/Channel/ReserveProps.lean`, `LnLean/Proofs/Common.lean` | `step_*` preservation lemmas | same balance/HTLC invariance assumption |

All of those files are outside this lane's edit set, so the relation remains
separate and embeds `Step`.  `Step.update_add_htlc` is provided as an `abbrev`
(definition, not a constructor) so callers can still write the requested name:

```lean
abbrev Step.update_add_htlc (hashFn : ByteArray → ByteArray) (c : Channel)
    (hphase : c.phase = ChannelPhase.normal) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (haff : AffordableAdd c dir amount cltv) :
    UpdateStep hashFn c (.addHtlc dir amount ph cltv)
      (updateAddHtlc c dir amount ph cltv)
```

---

## 2. Exact signatures — `LnLean/Channel/State.lean` (additive)

```lean
def pendingHtlcValueOf (c : Channel) : Nat

def offeredBalance (c : Channel) : Direction → Msat

def offeringReserveSat (c : Channel) : Direction → Nat

def receiverParams (c : Channel) : Direction → ChannelParams

structure AffordableAdd (c : Channel) (dir : Direction) (amount : Msat)
    (cltvExpiry : Height) : Prop where
  positive : 0 < amount.val
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  withinInFlight :
    pendingHtlcValueOf c + amount.val ≤ (receiverParams c dir).maxHtlcValue.val

def updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : Channel

def mapHtlcAt (i : Nat) (f : HTLC → HTLC) (hs : List HTLC) : List HTLC

def setHtlcStateAt (hs : List HTLC) (i : Nat) (st : HTLCState) : List HTLC

def failHtlcAt (c : Channel) (i : Nat) : Channel

def fulfillHtlcAt (c : Channel) (i : Nat) : Channel

inductive UpdateEvent where
  | lifecycle (e : ProtocolEvent)
  | addHtlc (direction : Direction) (amount : Msat) (paymentHash : PaymentHash)
      (cltvExpiry : Height)
  | fulfillHtlc (index : Nat) (preimage : Preimage)
  | failHtlc (index : Nat)

inductive UpdateStep (hashFn : ByteArray → ByteArray) :
    Channel → UpdateEvent → Channel → Prop where
  | lifecycle {c c' : Channel} {e : ProtocolEvent} (h : Step c e c') :
      UpdateStep hashFn c (.lifecycle e) c'
  | update_add_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
      (haff : AffordableAdd c dir amount cltv) :
      UpdateStep hashFn c (.addHtlc dir amount ph cltv)
        (updateAddHtlc c dir amount ph cltv)
  | update_fulfill_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (i : Nat) (h : HTLC) (p : Preimage)
      (hi : c.htlcs[i]? = some h) (hpending : h.isPending)
      (hpre : p.Valid ∧ hashFn p.bytes = h.paymentHash.bytes) :
      UpdateStep hashFn c (.fulfillHtlc i p) (fulfillHtlcAt c i)
  | update_fail_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (i : Nat) (h : HTLC) (hi : c.htlcs[i]? = some h)
      (hpending : h.isPending) :
      UpdateStep hashFn c (.failHtlc i) (failHtlcAt c i)

inductive UpdateReachable (hashFn : ByteArray → ByteArray) :
    Channel → Channel → Prop where
  | refl (c : Channel) : UpdateReachable hashFn c c
  | step {a b c : Channel} {e : UpdateEvent} :
      UpdateReachable hashFn a b → UpdateStep hashFn b e c →
        UpdateReachable hashFn a c
```

The three concrete successors are total functions (out-of-range index is a
no-op); the relation guards rule the degenerate cases out by requiring
`c.htlcs[i]? = some h` and `h.isPending`.

---

## 3. Exact signatures — `LnLean/Proofs/Channel/StateTransitionTargets.lean`

For readability, `E37` abbreviates the namespace `LnLean.Proofs.WaveE.E37`,
`ReserveInvariant` abbreviates `LnLean.Proofs.Channel.ReserveInvariant`,
`localReserveSat`/`remoteReserveSat` abbreviate the corresponding
`LnLean.Proofs.Channel` definitions, and `pendingHtlcValueOf`,
`updateAddHtlc`, `failHtlcAt`, `fulfillHtlcAt` are the
`LnLean.Channel` definitions from §2.  The signatures below were verified with
`#check` against those fully qualified names.

### 3.1 Pending bucket and successor algebra

```lean
theorem pendingHtlcValueOf_eq_listPending (c : Channel) :
  pendingHtlcValueOf c = listPending c.htlcs

theorem listPending_eq_sum_contribution (hs : List HTLC) :
  listPending hs = (List.map contribution hs).sum

theorem listPending_cons (h : HTLC) (hs : List HTLC) :
  listPending (h :: hs) = contribution h + listPending hs

theorem contribution_eq_zero_of_settled {h : HTLC}
  (hs : h.state = HTLCState.fulfilled ∨ h.state = HTLCState.failed ∨
    h.state = HTLCState.removed) : contribution h = 0

theorem contribution_eq_amount_of_pending {h : HTLC}
  (hp : h.state = HTLCState.offered ∨ h.state = HTLCState.received) :
  contribution h = h.amount.val

theorem listPending_mapHtlcAt_settle (st : HTLCState)
  (hst : st = HTLCState.fulfilled ∨ st = HTLCState.failed ∨
    st = HTLCState.removed) (i : Nat) (hs : List HTLC)
  (x : HTLC) (hi : hs[i]? = some x) :
  listPending hs =
    listPending (mapHtlcAt i (fun h => { h with state := st }) hs) +
      contribution x

theorem pendingHtlcValueOf_settleAt (c : Channel) (i : Nat) (st : HTLCState)
  (hst : st = HTLCState.fulfilled ∨ st = HTLCState.failed ∨
    st = HTLCState.removed) (h : HTLC)
  (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
  pendingHtlcValueOf c = listPending (setHtlcStateAt c.htlcs i st) + h.amount.val

theorem updateAddHtlc_htlcs (c : Channel) (dir : Direction) (amount : Msat)
  (ph : PaymentHash) (cltv : Height) :
  (updateAddHtlc c dir amount ph cltv).htlcs =
    c.htlcs ++ [{ direction := dir, amount := amount, paymentHash := ph,
                  cltvExpiry := cltv,
                  state := match dir with
                    | .local => HTLCState.offered
                    | .remote => HTLCState.received }]

theorem failHtlcAt_htlcs (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) :
  (failHtlcAt c i).htlcs = setHtlcStateAt c.htlcs i HTLCState.failed

theorem fulfillHtlcAt_htlcs (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) :
  (fulfillHtlcAt c i).htlcs = setHtlcStateAt c.htlcs i HTLCState.fulfilled

theorem pendingHtlcValueOf_updateAddHtlc (c : Channel) (dir : Direction)
  (amount : Msat) (ph : PaymentHash) (cltv : Height) :
  pendingHtlcValueOf (updateAddHtlc c dir amount ph cltv) =
    pendingHtlcValueOf c + amount.val

theorem pendingHtlcValueOf_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
  pendingHtlcValueOf c = pendingHtlcValueOf (failHtlcAt c i) + h.amount.val

theorem pendingHtlcValueOf_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) (hp : h.isPending) :
  pendingHtlcValueOf c = pendingHtlcValueOf (fulfillHtlcAt c i) + h.amount.val
```

### 3.2 Balance and ledger

```lean
theorem balanceVal_updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
  (ph : PaymentHash) (cltv : Height)
  (hfit : amount.val ≤ (offeredBalance c dir).val) :
  (updateAddHtlc c dir amount ph cltv).balance.localBalance.val +
      (updateAddHtlc c dir amount ph cltv).balance.remoteBalance.val =
    c.balance.localBalance.val + c.balance.remoteBalance.val - amount.val

theorem balanceVal_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) :
  (failHtlcAt c i).balance.localBalance.val +
      (failHtlcAt c i).balance.remoteBalance.val =
    c.balance.localBalance.val + c.balance.remoteBalance.val + h.amount.val

theorem balanceVal_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) :
  (fulfillHtlcAt c i).balance.localBalance.val +
      (fulfillHtlcAt c i).balance.remoteBalance.val =
    c.balance.localBalance.val + c.balance.remoteBalance.val + h.amount.val

theorem failHtlcAt_balance_ge (c : Channel) (i : Nat) :
  c.balance.localBalance.val ≤ (failHtlcAt c i).balance.localBalance.val ∧
    c.balance.remoteBalance.val ≤ (failHtlcAt c i).balance.remoteBalance.val

theorem fulfillHtlcAt_balance_ge (c : Channel) (i : Nat) :
  c.balance.localBalance.val ≤ (fulfillHtlcAt c i).balance.localBalance.val ∧
    c.balance.remoteBalance.val ≤ (fulfillHtlcAt c i).balance.remoteBalance.val

theorem pendingValue_eq_pendingHtlcValueOf (c : Channel) :
  E37.pendingValue c = pendingHtlcValueOf c

theorem ledgerValue_eq (c : Channel) (fee : Msat) :
  E37.ledgerValue c fee =
    c.balance.localBalance.val + c.balance.remoteBalance.val +
      pendingHtlcValueOf c + fee.val

theorem committedAdd_eq_updateAddHtlc (c : Channel) (amount : Msat) :
  E37.committedAdd c amount =
    updateAddHtlc c Direction.local amount { bytes := ByteArray.empty } 0

theorem affordableAdd_implies_e37 {c : Channel} {amount : Msat}
  (h : AffordableAdd c Direction.local amount 0) :
  E37.AffordableCommittedAdd c amount

theorem ledgerValue_updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
  (ph : PaymentHash) (cltv : Height) (fee : Msat)
  (haff : AffordableAdd c dir amount cltv) :
  E37.ledgerValue (updateAddHtlc c dir amount ph cltv) fee =
    E37.ledgerValue c fee

theorem ledgerValue_failHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) (hp : h.isPending) (fee : Msat) :
  E37.ledgerValue (failHtlcAt c i) fee = E37.ledgerValue c fee

theorem ledgerValue_fulfillHtlcAt (c : Channel) (i : Nat) (h : HTLC)
  (hi : c.htlcs[i]? = some h) (hp : h.isPending) (fee : Msat) :
  E37.ledgerValue (fulfillHtlcAt c i) fee = E37.ledgerValue c fee

theorem ledgerValue_step {c c' : Channel} {e : ProtocolEvent}
  (h : Step c e c') (fee : Msat) :
  E37.ledgerValue c' fee = E37.ledgerValue c fee

theorem step_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
  (h : Step c e c') : c'.fundingValue = c.fundingValue
```

### 3.3 Main conservation / refinement theorem

```lean
theorem updateStep_preserves_ledger {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {e : UpdateEvent} (hs : UpdateStep hashFn c e c') (fee : Msat)
  (hled : E37.ledgerValue c fee = c.fundingValue.val) :
  E37.ledgerValue c' fee = c'.fundingValue.val

theorem updateStep_add_local_ledger_via_E37 (c : Channel) (fee amount : Msat)
  (haff : AffordableAdd c Direction.local amount 0)
  (hled : E37.ledgerValue c fee = c.fundingValue.val) :
  E37.ledgerValue (E37.committedAdd c amount) fee =
    (E37.committedAdd c amount).fundingValue.val
```

`updateStep_preserves_ledger` is proved **by cases on the constructor**.  For
`update_add_htlc`, `pendingHtlcValueOf` grows by `amount` while the offering
balance drops by `amount`; `fitsOffered` is exactly the hypothesis that makes
the latter a non-truncating `Nat.sub`.  For fulfil/fail, the pending bucket
drops by the selected record's amount and the same amount is credited to a
balance, so the sum is unchanged.  The lifecycle case reuses
`ledgerValue_step`.

### 3.4 Determinism, counters, reserve, reachability

```lean
theorem updateStep_deterministic {hashFn : ByteArray → ByteArray}
  {c c₁ c₂ : Channel} {e : UpdateEvent}
  (h₁ : UpdateStep hashFn c e c₁) (h₂ : UpdateStep hashFn c e c₂) : c₁ = c₂

theorem updateStep_phaseRank_le {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {e : UpdateEvent} (h : UpdateStep hashFn c e c') :
  phaseRank c.phase ≤ phaseRank c'.phase

theorem updateStep_add_counters {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {dir : Direction} {amount : Msat}
  {ph : PaymentHash} {cltv : Height}
  (h : UpdateStep hashFn c (UpdateEvent.addHtlc dir amount ph cltv) c') :
  c'.localCommitmentNumber = c.localCommitmentNumber ∧
    c'.remoteCommitmentNumber = c.remoteCommitmentNumber

theorem updateAddHtlc_reserveInvariant {c : Channel} {dir : Direction}
  {amount : Msat} {cltv : Height} (haff : AffordableAdd c dir amount cltv)
  (hres : ReserveInvariant c) :
  ReserveInvariant (updateAddHtlc c dir amount { bytes := ByteArray.empty } cltv)

theorem updateAddHtlc_inFlight_le {c : Channel} {dir : Direction}
  {amount : Msat} {cltv : Height} (haff : AffordableAdd c dir amount cltv) :
  pendingHtlcValueOf (updateAddHtlc c dir amount { bytes := ByteArray.empty } cltv) ≤
    (receiverParams c dir).maxHtlcValue.val

theorem reserveInvariant_of_balance_ge {c c' : Channel}
  (hlr : localReserveSat c' = localReserveSat c)
  (hrr : remoteReserveSat c' = remoteReserveSat c)
  (hl : c.balance.localBalance.val ≤ c'.balance.localBalance.val)
  (hr : c.balance.remoteBalance.val ≤ c'.balance.remoteBalance.val)
  (hres : ReserveInvariant c) : ReserveInvariant c'

theorem updateStep_preserves_reserve {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {e : UpdateEvent} (hs : UpdateStep hashFn c e c')
  (hres : ReserveInvariant c) : ReserveInvariant c'

theorem updateReachable_preserves_ledger {hashFn : ByteArray → ByteArray}
  {a b : Channel} (h : UpdateReachable hashFn a b) (fee : Msat)
  (hled : E37.ledgerValue a fee = a.fundingValue.val) :
  E37.ledgerValue b fee = b.fundingValue.val

theorem updateReachable_preserves_reserve {hashFn : ByteArray → ByteArray}
  {a b : Channel} (h : UpdateReachable hashFn a b)
  (hres : ReserveInvariant a) : ReserveInvariant b

theorem updateReachable_of_reachable {hashFn : ByteArray → ByteArray}
  {a b : Channel} (h : Reachable a b) : UpdateReachable hashFn a b
```

### 3.5 Guard extraction

```lean
theorem updateStep_add_affordable {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
  {cltv : Height}
  (h : UpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
  AffordableAdd c dir amount cltv

theorem updateStep_fail_pending {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {i : Nat} (h : UpdateStep hashFn c (.failHtlc i) c') :
  ∃ x, x ∈ c.htlcs ∧ x.isPending ∧ c' = failHtlcAt c i

theorem updateStep_fulfill_pending {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {i : Nat} {p : Preimage}
  (h : UpdateStep hashFn c (.fulfillHtlc i p) c') :
  ∃ x, x ∈ c.htlcs ∧ x.isPending ∧ p.Valid ∧
    hashFn p.bytes = x.paymentHash.bytes ∧ c' = fulfillHtlcAt c i

theorem updateStep_lifecycle_iff {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {e : ProtocolEvent} :
  UpdateStep hashFn c (.lifecycle e) c' ↔ Step c e c'
```

### 3.6 Non-vacuity and retained counterexample

```lean
theorem updateStep_add_witness :
  ∃ c c' e fee,
    UpdateStep (fun b => b) c e c' ∧
      E37.ledgerValue c fee = c.fundingValue.val ∧
      E37.ledgerValue c' fee = c'.fundingValue.val

theorem unguarded_add_ledger_counterexample :
  ∃ c dir amount ph cltv fee,
    E37.ledgerValue c fee = c.fundingValue.val ∧
      ¬ AffordableAdd c dir amount cltv ∧
      E37.ledgerValue (updateAddHtlc c dir amount ph cltv) fee ≠
        (updateAddHtlc c dir amount ph cltv).fundingValue.val

theorem updateStep_add_local_target (c : Channel) (amount : Msat)
  (hphase : c.phase = ChannelPhase.normal)
  (haff : AffordableAdd c Direction.local amount 0) :
  ∃ e c', UpdateStep (fun b => b) c e c' ∧
    c' = E37.committedAdd c amount
```

The witness is the concrete channel
`E37.testChannel 1000 1000 2000 0 1 1000` with a 500-msat local HTLC and zero
fee.  The counterexample is `E37.testChannel 0 1000 1000 0 0 0` with a 1-msat
local HTLC: `fitsOffered` fails, and the unguarded successor has ledger 1001
against funding 1000.

---

## 4. Build and verification evidence

All builds were run from `/home/ubuntu/ln-lean-repair` under the shared lock
with `LEAN_NUM_THREADS=1`.

### 4.1 Lane modules

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.State LnLean.Proofs.Channel.StateTransitionTargets
```

Result: `Build completed successfully (17 jobs).` — **RC 0**.

### 4.2 Affected direct importers (including `StateMachineProps` and `E37`)

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.Laws LnLean.Proofs.Channel.BreachProps \
    LnLean.Proofs.Channel.FeeTargets LnLean.Proofs.Channel.ReserveProps \
    LnLean.Proofs.Channel.StateMachineProps LnLean.Proofs.Common \
    LnLean.Proofs.Liveness LnLean.Proofs.ModelHardening.F03 \
    LnLean.Proofs.ModelHardening.F11 LnLean.Proofs.Payment.LiquidityProps \
    LnLean.Proofs.Protocol.ChannelReestablishProps \
    LnLean.Proofs.WaveD.D11 LnLean.Proofs.WaveD.D12 \
    LnLean.Proofs.WaveD.D13 LnLean.Proofs.WaveD.D14 \
    LnLean.Proofs.WaveE.E37
```

Result: `Build completed successfully (140 jobs).` — **RC 0**.  The only
warnings were pre-existing `if_pos`/`if_neg` deprecations in
`LnLean/Proofs/Routing/GossipProps.lean`, an unrelated transitive dependency.

`LnLean.Proofs.Channel.StateMachineProps` and `LnLean.Proofs.WaveE.E37` both
rebuilt green, so the additive layer did not disturb the phase-transition proof
or the E37 counter-model.

### 4.3 Axioms

`#print axioms` over the public surface (scratch script outside the tree):

```text
updateStep_preserves_ledger                          [propext, Quot.sound]
updateStep_preserves_reserve                         [propext, Quot.sound]
updateReachable_preserves_ledger                     [propext, Quot.sound]
updateReachable_preserves_reserve                    [propext, Quot.sound]
committedAdd_eq_updateAddHtlc                        does not depend on any axioms
affordableAdd_implies_e37                            does not depend on any axioms
updateStep_deterministic                             [propext]
updateStep_phaseRank_le                              [propext, Quot.sound]
updateStep_add_counters                              [propext]
updateAddHtlc_reserveInvariant                       [propext]
updateAddHtlc_inFlight_le                            [propext, Quot.sound]
updateStep_add_affordable                            [propext]
updateStep_fail_pending                              [propext]
updateStep_fulfill_pending                           [propext]
updateStep_lifecycle_iff                             [propext]
updateStep_add_witness                               [propext, Quot.sound]
unguarded_add_ledger_counterexample                  [propext, Quot.sound]
updateStep_add_local_target                          [propext]
updateStep_add_local_ledger_via_E37                  [propext, Quot.sound]
ledgerValue_updateAddHtlc                            [propext, Quot.sound]
ledgerValue_failHtlcAt                               [propext, Quot.sound]
ledgerValue_fulfillHtlcAt                            [propext, Quot.sound]
updateReachable_of_reachable                         [propext]
```

No theorem depends on `Classical.choice`; nothing depends on an unapproved
axiom.  `updateStep_add_witness` is a closed existential, so the new relation
is inhabited.

### 4.4 Forbidden-construct scan

```sh
grep -nE "sorry|axiom|admit|native_decide|unsafe|implemented_by" \
  LnLean/Channel/State.lean LnLean/Proofs/Channel/StateTransitionTargets.lean
```

Result: **no matches** (exit status 1 / empty output).

---

## 5. Compatibility notes

1. **No `Channel` field was added.**  `updateAddHtlc`, `failHtlcAt`, and
   `fulfillHtlcAt` are functions on the existing record; therefore there are
   **no record-literal migration sites** anywhere in the tree.
2. **No `Step` or `ProtocolEvent` constructor was added or removed.**
   `LnLean.Proofs.Liveness.step?`, `step?_sound`, `step?_complete`, and every
   `Step`-shaped preservation theorem compile unchanged.
3. **No existing declaration in `State.lean` was modified.**  `git diff
   --numstat` reports `228  0` for the file (append-only).
4. **Name clash avoided.**  This module deliberately uses
   `pendingHtlcValueOf`, because `LnLean.Proofs.Channel.BreachProps` already
   defines `LnLean.Channel.pendingHtlcValue`.  Do not rename it without
   renaming the BreachProps definition.
5. **Index-based settlement.**  `HTLC` has no id field.  `UpdateEvent.fulfillHtlc`
   and `.failHtlc` carry a `Nat` index, and the constructor guard requires
   `c.htlcs[i]? = some h` with `h.isPending`.  If an HTLC id is added later,
   these two events and `mapHtlcAt` are the migration points.
6. **Hash function is a parameter.**  `UpdateStep hashFn` and
   `fulfillHtlcAt` take `hashFn : ByteArray → ByteArray`; preimage soundness is
   conditional on `p.Valid ∧ hashFn p.bytes = x.paymentHash.bytes`, matching
   `LnLean.Channel.HTLC.fulfillHTLC`.  No cryptographic assumption is asserted.

### If the parent later wants a real `Step` constructor

This lane did **not** do it, and it cannot be done inside the owned files.  The
minimal migration patch would be:

1. `LnLean/Channel/State.lean`: add `ProtocolEvent.updateAddHtlc …` and a
   `Step.update_add_htlc` constructor (or fold `UpdateStep` into `Step`), then
   delete the `abbrev` shim.
2. `LnLean/Proofs/Liveness.lean`: add the executable `step?` branch and extend
   `step?_sound` / `step?_complete`.
3. `LnLean/Proofs/Channel/StateMachineProps.lean`: add the
   `update_add_htlc` branch to `step_allowedPhaseTransition` (requires
   `c.phase = normal` to be the target phase).
4. `LnLean/Proofs/Payment/LiquidityProps.lean`,
   `LnLean/Proofs/ModelHardening/F03.lean`,
   `LnLean/Proofs/WaveD/D14.lean`,
   `LnLean/Proofs/PhaseC2/LivenessDelivery.lean`,
   `LnLean/Channel/Laws.lean`,
   `LnLean/Proofs/Channel/ReserveProps.lean`,
   `LnLean/Proofs/Common.lean`: restate the invariance lemmas with an explicit
   `UpdateStep`/HTLC-update premise, or move them to the update relation.
5. Re-run `scripts/regen-root.sh` (generated `LnLean.lean`) and the full
   audit.

Until then, consumers should use `UpdateStep` for HTLC messages and `Step` for
lifecycle messages, with `UpdateStep.lifecycle` as the bridge.

---

## 6. Integration steps (parent-owned; not performed here)

1. **Root import.**  Do not hand-edit `LnLean.lean` (it is generated by
   `scripts/regen-root.sh`).  Regenerate so that
   `import LnLean.Proofs.Channel.StateTransitionTargets` appears in the root.
2. **Obligation catalog (`MODEL-02` / `LN-CH-101`).**  Suggested replacement
   for the current `docs/OPEN-ISSUES.md:53` row:

   ```text
   | `MODEL-02` | P2 | addressed | HTLC update messages are modelled additively | `LN-CH-101`: `UpdateStep` adds `update_add_htlc`/`update_fulfill_htlc`/`update_fail_htlc`; `updateStep_preserves_ledger` proves conservation from the constructor and `committedAdd_eq_updateAddHtlc` refines E37 |
   ```

   The literal lifecycle `Step.update_add_htlc` constructor remains
   intentionally absent; that is now a scoping decision, not a proof gap.
3. **Traceability.**  Add rows mapping `MODEL-02` / `LN-CH-101` to:
   `LnLean.Proofs.Channel.StateTransitionTargets.updateStep_preserves_ledger`,
   `updateStep_preserves_reserve`,
   `updateReachable_preserves_ledger`,
   `committedAdd_eq_updateAddHtlc`,
   `affordableAdd_implies_e37`,
   `updateStep_add_affordable`.
4. **Axiom audit.**  Add
   `LnLean.Proofs.Channel.StateTransitionTargets` to the audited module list.
   Expected dependencies are only `propext` and `Quot.sound`.
5. **Theorem index / docs.**  If the project documents `Step` as *the* channel
   state machine, add one sentence that `UpdateStep` is the HTLC-update layer
   and `Step` remains the lifecycle layer.

No Git writes were performed.

---

## 7. Scope caveats (not modelled)

- The commitment dance (`commitment_signed` / `revoke_and_ack`) that turns a
  pending update into a signed commitment.  `UpdateStep` records the message
  effect only.
- Second-stage fees and dust trimming of the added HTLC output.
- `update_fee`, `shutdown`, and `closing_signed` already live in `Step`; they
  are reachable through `UpdateStep.lifecycle`.
- HTLC ids (see §5.5) and onion-level failure reasons.
- Cryptographic binding of `paymentHash`/`preimage`: this is an explicit
  hypothesis on `hashFn`, not a theorem about SHA-256.

## 8. Files and line anchors

- `LnLean/Channel/State.lean`
  - `pendingHtlcValueOf` line 261
  - `AffordableAdd` line 295
  - `updateAddHtlc` line 318
  - `update_fulfill_htlc` / `update_fail_htlc` successors lines 353, 373
  - `UpdateEvent` line 393
  - `UpdateStep` line 409
  - `UpdateReachable` line 436
  - `Step.update_add_htlc` shim line 448
- `LnLean/Proofs/Channel/StateTransitionTargets.lean`
  - pending-bucket algebra lines 60–185
  - successor algebra lines 186–334
  - E37 bridge and ledger conservation lines 336–457
  - determinism / counters / reserve / reachability lines 459–624
  - guard extraction / non-vacuity / counterexample lines 626–736
