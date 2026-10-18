# S6-MODEL-DANCE — ordered `commitment_signed` / `revoke_and_ack` round

**Lane:** `S6-MODEL-DANCE` (`MODEL-03`, `MODEL-02`).
**Repository:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` at `201a0a0` (wave-6 launch).
**Verdict:** complete for the assigned additive scope.  The commitment round is
now a separate ordered relation `DanceStep` over the existing `Channel` record.
Its reachable states satisfy the round-window invariant, never expose a revoked
commitment as current, advance the revocation watermark monotonically, and
preserve balance, HTLCs, funding value, the E37 ledger, and the reserve
invariant.  Every dance trace embeds into both the lifecycle `Step` relation and
the wave-5 `UpdateStep` relation.  The unguarded lifecycle relation is unchanged
and still has its wave-5 `update_add_htlc` counterexample; three new
counterexamples show why the dance guards are load-bearing.

- Lane files:
  - `LnLean/Channel/State.lean` — additive layer at lines 458–562
    (`git diff --numstat`: `109  1`; the only changed existing line is one
    module-docstring bullet).
  - `LnLean/Proofs/Channel/CommitmentDanceTargets.lean` — new, 652 lines.
  - `agents/reports/swarm6/S6-MODEL-DANCE.md` — this report.
- Not modified: `LnLean/Proofs/Liveness.lean`, `LnLean/Proofs/WaveD/D14.lean`,
  `LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`,
  `scripts/check-final.py`, shared docs/scripts, other lanes' files, `vendor/**`.
  No Git write commands (commit/push/branch) were run.
- The other modified/untracked files visible in `git status` belong to
  concurrent lanes and were left untouched.

## 1. Result in one paragraph

Wave 5 added the HTLC update messages as the additive `UpdateStep` relation but
left the round that commits them abstract.  This lane adds the missing
`commitment_signed`/`revoke_and_ack` ordering without changing
`ProtocolEvent`, `Step`, the executable `step?` scheduler, or any existing
balance/HTLC theorem.  `DanceStep` allows `commitment_signed` only when
`remoteCommitmentNumber = localCommitmentNumber` and `revoke_and_ack` only when
`remoteCommitmentNumber = localCommitmentNumber + 1`; both require the `normal`
phase.  The target functions change exactly one commitment counter and nothing
else.  From the constructors the lane proves the round window
`local ≤ remote ≤ local + 1` on every non-reflexive `DanceReachable` target,
`commitmentGap` transitions `0 → 1 → 0`, both counters are monotone, a
`revoke_and_ack` revokes exactly the previous local commitment, revoked indices
are never current, and ledger/reserve preservation lifts to traces.  A concrete
two-round witness reaches counters `2/2` with commitments `0` and `1` revoked,
and three counterexamples show that unguarded `Step` can double-sign, revoke
from idle, and sign an already-revoked commitment.  The build is green
(`19 jobs`) and the axiom surface is only `propext`, `Quot.sound`, and one use
of `Classical.choice`.

## 2. What is mechanized

### 2.1 The additive layer in `State.lean`

`DanceEvent` is deliberately separate from `ProtocolEvent`:

```lean
inductive DanceEvent where
  | commitmentSigned
  | revokeAndAck
deriving Repr, DecidableEq, BEq
```

`DanceEvent.toProtocolEvent` maps the two constructors to the existing
`ProtocolEvent.commitmentSigned` and `ProtocolEvent.revokeAndAck`
(`State.lean:70-71`).  No message vocabulary is added.

`DanceStep` is the ordered relation:

```lean
inductive DanceStep : Channel → DanceEvent → Channel → Prop where
  | commitmentSigned (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
      DanceStep c DanceEvent.commitmentSigned (signRemoteCommitment c)
  | revokeAndAck (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
      DanceStep c DanceEvent.revokeAndAck (revokeLocalCommitment c)
```

where

```lean
def signRemoteCommitment (c : Channel) : Channel :=
  { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }

def revokeLocalCommitment (c : Channel) : Channel :=
  { c with localCommitmentNumber := c.localCommitmentNumber + 1 }
```

The guards are the two halves of one round.  An idle state can sign; a state
with one signature outstanding can revoke; the opposite combinations are
excluded by `no_commitmentSigned_with_round_in_flight` and
`no_revokeAndAck_without_commitmentSigned`.  `DanceReachable` is the
reflexive-transitive closure, exactly parallel to `Reachable` and
`UpdateReachable`.

### 2.2 Round window and guard necessity

`DanceOrdered c` is `local ≤ remote ∧ remote ≤ local + 1`, and
`commitmentGap c` is `remote - local`.  The mechanized facts are:

- every dance source and target is ordered (`danceStep_source_ordered`,
  `danceStep_ordered`);
- every non-reflexive reachable target is ordered
  (`danceReachable_ordered`), with the reflexive form
  `danceReachable_ordered_or_eq : a = b ∨ DanceOrdered b`;
- a signing step takes the gap from `0` to `1`; the matching revocation takes
  it from `1` to `0` (`commitmentGap_signRemoteCommitment_of_idle`,
  `commitmentGap_revokeLocalCommitment_of_pending`);
- a complete round advances both counters by exactly one and returns to an
  idle window (`dance_round_closes`).

The guards are not vacuous.  `unguarded_double_commitmentSigned_breaks_ordering`
exhibits two consecutive `Step.commitmentSigned` messages whose target violates
`DanceOrdered`; `unguarded_revokeAndAck_from_idle_breaks_ordering` exhibits a
`Step.revokeAndAck` from an idle channel whose target also violates it.

### 2.3 Revocation ordering and no stale commitment

`CommitmentRevoked c i` is the local watermark `i < c.localCommitmentNumber`.
This is the model's view of “the per-commitment secret for `i` has already been
revealed”.  The lane proves:

- both counters are monotone along a dance step and along a dance trace
  (`danceStep_local_le`, `danceStep_remote_le`, `danceReachable_local_le`,
  `danceReachable_remote_le`);
- revocation is monotone (`commitmentRevoked_mono`,
  `danceReachable_revoked_mono`);
- the current local commitment is never revoked
  (`commitmentRevoked_current_local`), and in an ordered state neither is the
  current remote commitment (`commitmentRevoked_current_remote`);
- `revoke_and_ack` revokes exactly the previous local commitment
  (`revokeAndAck_revokes_previous`);
- a `commitment_signed` source's remote commitment is not already revoked
  (`commitmentSigned_source_remote_not_revoked`);
- along a non-reflexive trace, an index revoked at the start is never the
  current local or remote commitment
  (`danceReachable_revoked_never_current`), and neither current commitment is
  revoked (`danceReachable_current_not_revoked`).

The unguarded relation has the corresponding negative result:
`unguarded_step_signs_revoked_commitment` performs a `revoke_and_ack` from idle
and then signs remote commitment `0` while the local watermark already marks it
revoked.

### 2.4 Balance, ledger, and reserve preservation

A dance step changes only `localCommitmentNumber` or
`remoteCommitmentNumber`; every other `Channel` field is definitionally
unchanged.  The module therefore proves, by `rfl` and the wave-5 definitions:

- `danceStep_balance_eq`, `danceStep_htlcs_eq`,
  `danceStep_pendingHtlcValueOf`, `danceStep_fundingValue_eq`;
- `danceStep_ledgerValue` and `danceStep_preserves_ledger` for E37's
  `ledgerValue`;
- `danceStep_preserves_reserve` for `ReserveInvariant`;
- the trace forms `danceReachable_preserves_ledger` and
  `danceReachable_preserves_reserve`.

There is no new conservation assumption.  The ledger statement is conditional
only on the same pre-state ledger equation used by wave 5:
`E37.ledgerValue c fee = c.fundingValue.val`.

### 2.5 Compatibility with `Step` and `UpdateStep`

`DanceStep.toStep` proves every dance step is the corresponding unguarded
`Step`; the dance layer is a refinement, not a second semantics.
`danceStep_toUpdateStep` embeds every dance step as
`UpdateStep lifecycle`, and `danceReachable_toUpdateReachable` /
`danceReachable_toReachable` lift the embedding to traces.  Consequently the
wave-5 ledger and reserve theorems apply verbatim through
`danceReachable_preserves_ledger_via_update` and
`danceReachable_preserves_reserve_via_update`.

The existing unguarded-add counterexample is re-exported unchanged as
`unguarded_add_ledger_counterexample_retained`, so a dance consumer still sees
that `AffordableAdd` is load-bearing.

### 2.6 Non-vacuity

`dance_two_rounds_witness` starts from
`E37.testChannel 1000 1000 2000 0 1 1000` and performs

```text
commitment_signed → revoke_and_ack → commitment_signed → revoke_and_ack
```

ending with `localCommitmentNumber = 2`, `remoteCommitmentNumber = 2`,
commitments `0` and `1` revoked, `DanceOrdered` true, and the ledger preserved.
The existential is closed (no hypotheses), so the relation is inhabited.

## 3. Exact signatures

Namespace for the proof module:
`LnLean.Proofs.Channel.CommitmentDanceTargets`.
`E37` below abbreviates `LnLean.Proofs.WaveE.E37`; `ReserveInvariant`
abbreviates `LnLean.Proofs.Channel.ReserveInvariant`.

### 3.1 Declarations in `LnLean.Channel`

```lean
inductive DanceEvent where
  | commitmentSigned
  | revokeAndAck
deriving Repr, DecidableEq, BEq

DanceEvent.toProtocolEvent : DanceEvent → ProtocolEvent
DanceOrdered (c : Channel) : Prop
commitmentGap (c : Channel) : Nat
CommitmentRevoked (c : Channel) (i : Nat) : Prop
signRemoteCommitment (c : Channel) : Channel
revokeLocalCommitment (c : Channel) : Channel
DanceStep : Channel → DanceEvent → Channel → Prop
DanceStep.toStep {c c' : Channel} {e : DanceEvent} (h : DanceStep c e c') :
  Step c e.toProtocolEvent c'
DanceReachable : Channel → Channel → Prop
```

### 3.2 Successor projections

All are `rfl` lemmas; the `[simp]` attribute is on the declaration.

```lean
@[simp] theorem signRemoteCommitment_balance (c : Channel) :
  (signRemoteCommitment c).balance = c.balance
@[simp] theorem signRemoteCommitment_htlcs (c : Channel) :
  (signRemoteCommitment c).htlcs = c.htlcs
@[simp] theorem signRemoteCommitment_funding (c : Channel) :
  (signRemoteCommitment c).funding = c.funding
@[simp] theorem signRemoteCommitment_fundingValue (c : Channel) :
  (signRemoteCommitment c).fundingValue = c.fundingValue
@[simp] theorem signRemoteCommitment_phase (c : Channel) :
  (signRemoteCommitment c).phase = c.phase
@[simp] theorem signRemoteCommitment_localCommitmentNumber (c : Channel) :
  (signRemoteCommitment c).localCommitmentNumber = c.localCommitmentNumber
@[simp] theorem signRemoteCommitment_remoteCommitmentNumber (c : Channel) :
  (signRemoteCommitment c).remoteCommitmentNumber =
    c.remoteCommitmentNumber + 1

@[simp] theorem revokeLocalCommitment_balance (c : Channel) :
  (revokeLocalCommitment c).balance = c.balance
@[simp] theorem revokeLocalCommitment_htlcs (c : Channel) :
  (revokeLocalCommitment c).htlcs = c.htlcs
@[simp] theorem revokeLocalCommitment_funding (c : Channel) :
  (revokeLocalCommitment c).funding = c.funding
@[simp] theorem revokeLocalCommitment_fundingValue (c : Channel) :
  (revokeLocalCommitment c).fundingValue = c.fundingValue
@[simp] theorem revokeLocalCommitment_phase (c : Channel) :
  (revokeLocalCommitment c).phase = c.phase
@[simp] theorem revokeLocalCommitment_localCommitmentNumber (c : Channel) :
  (revokeLocalCommitment c).localCommitmentNumber =
    c.localCommitmentNumber + 1
@[simp] theorem revokeLocalCommitment_remoteCommitmentNumber (c : Channel) :
  (revokeLocalCommitment c).remoteCommitmentNumber =
    c.remoteCommitmentNumber
```

### 3.3 Guards, successors, and round window

```lean
theorem danceStep_commitmentSigned_requires_idle {c c' : Channel}
  (h : DanceStep c DanceEvent.commitmentSigned c') :
  c.remoteCommitmentNumber = c.localCommitmentNumber

theorem danceStep_revokeAndAck_requires_pending {c c' : Channel}
  (h : DanceStep c DanceEvent.revokeAndAck c') :
  c.remoteCommitmentNumber = c.localCommitmentNumber + 1

theorem danceStep_commitmentSigned_target {c c' : Channel}
  (h : DanceStep c DanceEvent.commitmentSigned c') :
  c' = signRemoteCommitment c

theorem danceStep_revokeAndAck_target {c c' : Channel}
  (h : DanceStep c DanceEvent.revokeAndAck c') :
  c' = revokeLocalCommitment c

theorem no_commitmentSigned_with_round_in_flight {c c' : Channel}
  (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
  ¬DanceStep c DanceEvent.commitmentSigned c'

theorem no_revokeAndAck_without_commitmentSigned {c c' : Channel}
  (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
  ¬DanceStep c DanceEvent.revokeAndAck c'

theorem commitmentGap_signRemoteCommitment_of_idle {c : Channel}
  (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
  commitmentGap (signRemoteCommitment c) = 1

theorem commitmentGap_revokeLocalCommitment_of_pending {c : Channel}
  (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
  commitmentGap (revokeLocalCommitment c) = 0

theorem danceStep_source_ordered {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') : DanceOrdered c

theorem danceStep_ordered {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') : DanceOrdered c'

theorem danceReachable_ordered_or_eq {a b : Channel}
  (h : DanceReachable a b) : a = b ∨ DanceOrdered b

theorem danceReachable_ordered {a b : Channel}
  (h : DanceReachable a b) (hne : a ≠ b) : DanceOrdered b
```

### 3.4 Counter monotonicity and revocation

```lean
theorem danceStep_local_le {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') :
  c.localCommitmentNumber ≤ c'.localCommitmentNumber

theorem danceStep_remote_le {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') :
  c.remoteCommitmentNumber ≤ c'.remoteCommitmentNumber

theorem danceStep_commitmentSigned_remote_strict {c c' : Channel}
  (h : DanceStep c DanceEvent.commitmentSigned c') :
  c.remoteCommitmentNumber < c'.remoteCommitmentNumber

theorem danceStep_revokeAndAck_local_strict {c c' : Channel}
  (h : DanceStep c DanceEvent.revokeAndAck c') :
  c.localCommitmentNumber < c'.localCommitmentNumber

theorem commitmentRevoked_mono {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') {i : Nat} (hr : CommitmentRevoked c i) :
  CommitmentRevoked c' i

theorem commitmentRevoked_current_local (c : Channel) :
  ¬CommitmentRevoked c c.localCommitmentNumber

theorem commitmentRevoked_current_remote {c : Channel}
  (ho : DanceOrdered c) :
  ¬CommitmentRevoked c c.remoteCommitmentNumber

theorem revokeAndAck_revokes_previous {c c' : Channel}
  (h : DanceStep c DanceEvent.revokeAndAck c') :
  CommitmentRevoked c' c.localCommitmentNumber

theorem commitmentSigned_source_remote_not_revoked {c c' : Channel}
  (h : DanceStep c DanceEvent.commitmentSigned c') :
  ¬CommitmentRevoked c c.remoteCommitmentNumber

theorem danceReachable_local_le {a b : Channel}
  (h : DanceReachable a b) :
  a.localCommitmentNumber ≤ b.localCommitmentNumber

theorem danceReachable_remote_le {a b : Channel}
  (h : DanceReachable a b) :
  a.remoteCommitmentNumber ≤ b.remoteCommitmentNumber

theorem danceReachable_revoked_mono {a b : Channel}
  (h : DanceReachable a b) {i : Nat} (hr : CommitmentRevoked a i) :
  CommitmentRevoked b i

theorem danceReachable_revoked_never_current {a b : Channel}
  (h : DanceReachable a b) (hne : a ≠ b) {i : Nat}
  (hr : CommitmentRevoked a i) :
  i ≠ b.localCommitmentNumber ∧ i ≠ b.remoteCommitmentNumber

theorem danceReachable_current_not_revoked {a b : Channel}
  (h : DanceReachable a b) (hne : a ≠ b) :
  ¬CommitmentRevoked b b.localCommitmentNumber ∧
    ¬CommitmentRevoked b b.remoteCommitmentNumber

theorem dance_round_closes {c c₁ c₂ : Channel}
  (h₁ : DanceStep c DanceEvent.commitmentSigned c₁)
  (h₂ : DanceStep c₁ DanceEvent.revokeAndAck c₂) :
  c₂.localCommitmentNumber = c.localCommitmentNumber + 1 ∧
    c₂.remoteCommitmentNumber = c.remoteCommitmentNumber + 1 ∧
    c₂.remoteCommitmentNumber = c₂.localCommitmentNumber ∧
    CommitmentRevoked c₂ c.localCommitmentNumber
```

### 3.5 Balance, ledger, and reserve

```lean
theorem danceStep_balance_eq {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') : c'.balance = c.balance

theorem danceStep_htlcs_eq {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') : c'.htlcs = c.htlcs

theorem danceStep_pendingHtlcValueOf {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') :
  pendingHtlcValueOf c' = pendingHtlcValueOf c

theorem danceStep_fundingValue_eq {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') : c'.fundingValue = c.fundingValue

theorem danceStep_ledgerValue {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') (fee : Msat) :
  E37.ledgerValue c' fee = E37.ledgerValue c fee

theorem danceStep_preserves_ledger {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') (fee : Msat)
  (hled : E37.ledgerValue c fee = c.fundingValue.val) :
  E37.ledgerValue c' fee = c'.fundingValue.val

theorem danceStep_preserves_reserve {c c' : Channel} {e : DanceEvent}
  (h : DanceStep c e c') (hres : ReserveInvariant c) :
  ReserveInvariant c'

theorem danceReachable_preserves_ledger {a b : Channel}
  (h : DanceReachable a b) (fee : Msat)
  (hled : E37.ledgerValue a fee = a.fundingValue.val) :
  E37.ledgerValue b fee = b.fundingValue.val

theorem danceReachable_preserves_reserve {a b : Channel}
  (h : DanceReachable a b) (hres : ReserveInvariant a) :
  ReserveInvariant b
```

### 3.6 Compatibility bridges

```lean
theorem danceStep_toUpdateStep {hashFn : ByteArray → ByteArray}
  {c c' : Channel} {e : DanceEvent} (h : DanceStep c e c') :
  UpdateStep hashFn c (UpdateEvent.lifecycle e.toProtocolEvent) c'

theorem danceReachable_toUpdateReachable {hashFn : ByteArray → ByteArray}
  {a b : Channel} (h : DanceReachable a b) : UpdateReachable hashFn a b

theorem danceReachable_toReachable {a b : Channel}
  (h : DanceReachable a b) : Reachable a b

theorem danceReachable_preserves_ledger_via_update
  {hashFn : ByteArray → ByteArray} {a b : Channel}
  (h : DanceReachable a b) (fee : Msat)
  (hled : E37.ledgerValue a fee = a.fundingValue.val) :
  E37.ledgerValue b fee = b.fundingValue.val

theorem danceReachable_preserves_reserve_via_update
  {hashFn : ByteArray → ByteArray} {a b : Channel}
  (h : DanceReachable a b) (hres : ReserveInvariant a) :
  ReserveInvariant b
```

### 3.7 Revocation-store view

```lean
def danceStore (c : Channel)
  (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
  RevocationStore

@[simp] theorem danceStore_minSeen (c : Channel)
  (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
  (danceStore c hbound).minSeen = c.localCommitmentNumber

theorem danceStore_isRevoked_iff (c : Channel)
  (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) (i : Nat) :
  LnLean.Channel.isRevoked (danceStore c hbound) i ↔
    CommitmentRevoked c i

theorem danceStore_revoke_previous {c c' : Channel}
  (h : DanceStep c DanceEvent.revokeAndAck c')
  (hbound : c'.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) :
  LnLean.Channel.isRevoked (danceStore c' hbound)
    c.localCommitmentNumber

theorem danceStore_revoked_index_bound (c : Channel)
  (hbound : c.localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT) {i : Nat}
  (hr : LnLean.Channel.isRevoked (danceStore c hbound) i) :
  i < COMMITMENT_SECRET_COUNT
```

### 3.8 Non-vacuity and counterexamples

```lean
theorem dance_two_rounds_witness :
  ∃ c c₁ c₂ c₃ c₄,
    DanceReachable c c₄ ∧
      DanceStep c DanceEvent.commitmentSigned c₁ ∧
        DanceStep c₁ DanceEvent.revokeAndAck c₂ ∧
          DanceStep c₂ DanceEvent.commitmentSigned c₃ ∧
            DanceStep c₃ DanceEvent.revokeAndAck c₄ ∧
              DanceOrdered c₄ ∧
                c₄.localCommitmentNumber = 2 ∧
                  c₄.remoteCommitmentNumber = 2 ∧
                    CommitmentRevoked c₄ 0 ∧
                      CommitmentRevoked c₄ 1 ∧
                        E37.ledgerValue c₄ { val := 0 } =
                          c₄.fundingValue.val

theorem unguarded_add_ledger_counterexample_retained :
  ∃ c dir amount ph cltv fee,
    E37.ledgerValue c fee = c.fundingValue.val ∧
      ¬AffordableAdd c dir amount cltv ∧
        E37.ledgerValue (updateAddHtlc c dir amount ph cltv) fee ≠
          (updateAddHtlc c dir amount ph cltv).fundingValue.val

theorem unguarded_double_commitmentSigned_breaks_ordering :
  ∃ c c₁ c₂,
    Step c ProtocolEvent.commitmentSigned c₁ ∧
      Step c₁ ProtocolEvent.commitmentSigned c₂ ∧ ¬DanceOrdered c₂

theorem unguarded_revokeAndAck_from_idle_breaks_ordering :
  ∃ c c', Step c ProtocolEvent.revokeAndAck c' ∧ ¬DanceOrdered c'

theorem unguarded_step_signs_revoked_commitment :
  ∃ c c₁ c₂,
    Step c ProtocolEvent.revokeAndAck c₁ ∧
      Step c₁ ProtocolEvent.commitmentSigned c₂ ∧
        CommitmentRevoked c₂ c₁.remoteCommitmentNumber
```

## 4. Build

Built only the owned modules under the shared lock, from
`/home/ubuntu/ln-lean-repair`:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.State \
    LnLean.Proofs.Channel.CommitmentDanceTargets \
    LnLean.Proofs.Channel.StateTransitionTargets
```

Result:

```text
Build completed successfully (19 jobs).
```

The three modules are `RC 0`.  `StateTransitionTargets` is included because the
dance layer reuses its wave-5 `UpdateStep`/ledger/reserve bridge and its
unguarded-add counterexample.

## 5. Axiom audit

`#print axioms` was run over every public theorem in the new module with a
scratch script outside the tree (`/tmp/opencode/axioms_dance.lean`).  The
observed union is

```text
{propext, Quot.sound, Classical.choice}
```

with no `sorryAx`, no `Lean.ofReduceBool`, and no unapproved axiom.  13
declarations are axiom-free; 36 depend only on subsets of the allowed set.
`Classical.choice` occurs once, in `danceStep_source_ordered`.  Selected rows:

```text
DanceStep.toStep                                      does not depend on any axioms
danceStep_commitmentSigned_requires_idle              does not depend on any axioms
danceStep_revokeAndAck_requires_pending               does not depend on any axioms
danceStep_source_ordered                              [propext, Classical.choice, Quot.sound]
danceStep_ordered                                     [propext, Quot.sound]
danceReachable_ordered                                [propext, Quot.sound]
danceReachable_revoked_never_current                  [propext, Quot.sound]
danceReachable_current_not_revoked                    [propext, Quot.sound]
dance_round_closes                                    [propext]
danceStep_balance_eq                                  does not depend on any axioms
danceStep_htlcs_eq                                    does not depend on any axioms
danceStep_pendingHtlcValueOf                          does not depend on any axioms
danceStep_preserves_ledger                            [propext, Quot.sound]
danceStep_preserves_reserve                           does not depend on any axioms
danceReachable_preserves_ledger                       [propext, Quot.sound]
danceReachable_preserves_reserve                      does not depend on any axioms
danceReachable_toReachable                            does not depend on any axioms
dance_two_rounds_witness                              [propext, Quot.sound]
unguarded_add_ledger_counterexample_retained          [propext, Quot.sound]
unguarded_double_commitmentSigned_breaks_ordering     [propext]
unguarded_revokeAndAck_from_idle_breaks_ordering      [propext]
unguarded_step_signs_revoked_commitment               [propext]
```

## 6. Forbidden-construct scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/CommitmentDanceTargets.lean
```

Result: no matches (empty output, exit status 1).

`git diff --numstat -- LnLean/Channel/State.lean` reports `109  1`.  The one
deletion is the replaced module-docstring sentence at `State.lean:40`; no
existing declaration was removed or changed.  The new proof module is 652
lines.

## 7. Why the dance was kept separate

`ProtocolEvent.commitmentSigned` and `ProtocolEvent.revokeAndAck` already exist
(`State.lean:70-71`), so folding the dance into the lifecycle relation would
**not** require new message vocabulary.  It would require changing the two
existing `Step` constructors to carry the idle/pending guards.  That is a
behavioural change to the shared lifecycle relation, not an additive one:

1. `step?` would have to reject a second `commitment_signed` while a round is in
   flight, and reject `revoke_and_ack` when no round is in flight.
2. `step?_sound` and `step?_complete` would need the guard extraction and
   reconstruction proofs.
3. Every explicit `Step.commitmentSigned`/`Step.revokeAndAck` pattern or
   application would need an extra hypothesis.  Wildcard `cases h` proofs would
   usually still typecheck, but their proof terms change.
4. The wave-5 `UpdateStep.lifecycle` bridge would silently inherit the stricter
   lifecycle relation.  That is sound for the dance but changes the meaning of
   “lifecycle step” for every consumer.

The separate layer gives the invariants now, keeps the unguarded relation and
its counterexamples intact, and leaves a clean migration path if the parent
later decides to make the guard part of `Step` itself.

### 7.1 Exact downstream migration list

The following is the set of declarations that pattern-match or apply the two
affected `Step` constructors, plus the invariant proofs that would need to be
recompiled and audited.  Line anchors are for base `201a0a0`.
“Source edit” means the explicit constructor pattern/application would no
longer elaborate after adding a guard field; “recompile” means the statement
remains true and only the proof term changes.

| File | Declarations | Effect if guards are folded into `Step` |
|---|---|---|
| `LnLean/Proofs/Liveness.lean` | `step?` (127), `step?_sound` (167), `step?_complete` (232), `step_event_of_awaitingLockin` (322), `noLoss_shuttingDown_eventually_closed` (674) | Source edit: `step?` must enforce the two guards; `step?_sound`, `step?_complete`, and `step_event_of_awaitingLockin` have explicit `commitmentSigned`/`revokeAndAck` patterns or applications. `noLoss_shuttingDown_eventually_closed` uses a wildcard `cases hs <;> simp_all` and should only recompile, but it sits on the same scheduler path and must be rechecked. |
| `LnLean/Proofs/Channel/StateMachineProps.lean` | `step_allowedPhaseTransition` (138), `step_phaseRank_eq_or_succ` (174), `step_preserves_identity` (187), `step_commitmentSigned_counters` (225), `step_revokeAndAck_counters` (235), `step_remote_eq_of_ne_commitmentSigned` (244), `step_local_eq_of_ne_revokeAndAck` (252), `step_remote_succ_iff` (259), `step_local_succ_iff` (274), `step_not_both_counters_succ` (290), `step_local_le_succ` (303), `step_remote_le_succ` (308) | Source edit for `step_allowedPhaseTransition` (explicit `cases h with`). The other eleven use wildcard `cases h` and should recompile; their statements remain true because only the guard hypotheses change. |
| `LnLean/Proofs/Payment/LiquidityProps.lean` | `step_preserves_balance` (567), `step_preserves_fundingValue` (572), `step_preserves_meetsReserve` (577) | Recompile; targets are unchanged, so the balance/funding/reserve statements remain true. |
| `LnLean/Proofs/ModelHardening/F03.lean` | `step_htlcs_eq` (287), `step_preserves_ledgerBalanced` (292) | Recompile; `Step` still does not touch HTLCs or the settled ledger. |
| `LnLean/Proofs/WaveD/D14.lean` | `waveD_d14_step_balance` (465), `waveD_d14_step_htlcs` (471), `waveD_d14_step_localReserveSat` (476), `waveD_d14_step_remoteReserveSat` (481), `waveD_d14_step_reserve_iff` (486), `waveD_d14_step_preserves_reserve` (504), `waveD_d14_step_exposure` (509) | Recompile; the strict `Step` still preserves the same fields. |
| `LnLean/Proofs/PhaseC2/LivenessDelivery.lean` | `step_htlcs_eq` (65), `runPrefix_htlcs` (70) | Recompile; no HTLC movement is introduced. |
| `LnLean/Channel/Laws.lean` | `step_commitment_numbers` (156), `commitmentSigned_remote_succ` (183), `revokeAndAck_local_succ` (191) | Recompile; the counter effects are unchanged, but proof terms see the extra guard. |
| `LnLean/Proofs/Channel/ReserveProps.lean` | `step_preserves_reserveWithinCapacity` (171), `step_preserves_reserveInvariant` (182), `step_preserves_channelHtlcBounds` (274), `step_preserves_valueConservation` (540) | Recompile; the reserve/conservation statements remain true. |
| `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` | `commitmentSigned_counters_strict` (478), `revokeAndAck_counters_strict` (488) | Source edit for the explicit constructor patterns; counter strictness remains true. |
| `LnLean/Proofs/WaveD/D13.lean` | `waveD_d13_FeeCheckedStep` (`lift` at 405), `waveD_d13_feeCheckedStep_step` (411), `waveD_d13_feeCheckedStep_commitmentSigned_sufficient` (421), `waveD_d13_feeCheckedStep_of_step_of_ne` (442), `waveD_d13_feeCheckedStep_commitmentSigned_iff` (450) | Source edit for `waveD_d13_FeeCheckedStep` / `_step`: `lift` accepts a `Step`, and `_step` reconstructs a guarded `Step.commitmentSigned`, so the checked relation needs the same idle guard or an explicit bridge hypothesis. `_sufficient`, `_of_step_of_ne`, and `_iff` should only recompile. |
| `LnLean/Proofs/Channel/FeeTargets.lean` | `checkedCommitmentSigned_iff_sufficient` (405), `exists_checkedCommitmentSigned_iff_sufficient` (420), `no_checkedCommitmentSigned_iff_insufficient` (438), `commitmentSigningGate_rejected_iff_no_checkedSigning` (452), `insufficient_no_checkedCommitmentSigned` (470), `commitment_rejected_before_signing` (485) | Recompile / restate the D13 bridge if `waveD_d13_FeeCheckedStep` gains a guard; the fee-gate statements themselves are unchanged. |

No declaration in the new dance module needs migration: `DanceStep.toStep` only
*uses* the unguarded constructors and remains valid.

## 8. Integration steps (parent-owned; not performed here)

1. **Root import.**  Do not hand-edit `LnLean.lean`; it is generated by
   `scripts/regen-root.sh`.  Regenerate so that
   `import LnLean.Proofs.Channel.CommitmentDanceTargets` appears in the root.
2. **Axiom audit.**  Add
   `LnLean.Proofs.Channel.CommitmentDanceTargets` to the audited module list in
   `AxiomAudit.lean` (or the equivalent script configuration).  Expected
   dependencies are subsets of `{propext, Quot.sound, Classical.choice}`.
3. **Catalog.**  `docs/OPEN-ISSUES.md:61` currently records `MODEL-03` as
   open.  Suggested replacement text:

   ```text
   | `MODEL-03` | P2 | addressed | Ordered commitment round is modelled additively | `DanceStep` restricts `commitment_signed` to an idle window and `revoke_and_ack` to one outstanding signature; `danceReachable_ordered`, `danceReachable_revoked_never_current`, `danceReachable_preserves_ledger`, and `danceReachable_preserves_reserve` prove the reachable-state invariants. `DanceStep.toStep` and `danceStep_toUpdateStep` preserve the existing layers. |
   ```

   `MODEL-02` can remain “addressed (mitigated)” with a cross-reference to the
   dance module; the dance does not add the deferred-update queue.
4. **Traceability.**  Add rows mapping `MODEL-03` / `MODEL-02` to
   `LnLean.Channel.DanceStep`,
   `LnLean.Proofs.Channel.CommitmentDanceTargets.danceReachable_ordered`,
   `danceReachable_revoked_never_current`,
   `danceReachable_current_not_revoked`,
   `danceReachable_preserves_ledger`, and
   `danceReachable_preserves_reserve`.
5. **Theorem index / docs.**  If the project describes `Step` as *the* channel
   state machine, add one sentence that `DanceStep` is the ordered commitment
   round over the same record and `UpdateStep` is the HTLC-update layer.
6. **Full gate.**  Re-run `scripts/check-final.py` and the project-wide build
   only after the root import and audit lists are regenerated in the parent
   worktree.

No `LnLean.lean`, `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, or
`scripts/check-final.py` edit was made in this lane.

## 9. Scope caveats (not modelled)

- **Pending-update queue.**  `DanceStep` changes counters only.  It does not
  model the queue of deferred `update_add_htlc`/`update_fulfill_htlc`/
  `update_fail_htlc` messages that a round commits.  A later composition of
  `UpdateStep` and `DanceStep` would need to encode that queue and the
  `channel_reestablish` replay rules.
- **Signatures and per-commitment material.**  The lane does not model the
  `commitment_signed` signature payload, per-commitment points, or the wire
  format.  `CommitmentSigned` in `LnLean.Protocol.Messages` is untouched.
- **BOLT 3 `2^48` bound.**  `Channel` does not enforce
  `localCommitmentNumber ≤ 2^48`.  `danceStore` takes
  `localCommitmentNumber ≤ COMMITMENT_SECRET_COUNT` as an explicit hypothesis;
  `danceStore_revoked_index_bound` returns the strict bound.  No arithmetic
  wrap-around is modelled.
- **Counter correspondence.**  `local` and `remote` are related by
  `DanceOrdered` only inside the ordered layer.  The unguarded `Step` can put
  `local` ahead of `remote`; that is exactly what the idle-revoke and
  sign-revoked counterexamples exhibit.
- **Revocation abstraction.**  `CommitmentRevoked` is a local watermark, and
  `danceStore` is a `RevocationStore` view with no slot contents.  The concrete
  shachain/secret derivation is abstract; only the watermark ordering and the
  `2^48` index bound are proved.
- **One round at a time.**  The guards allow at most one outstanding
  `commitment_signed` (`remote = local + 1`).  Batched or pipelined rounds are
  not modelled.

## 10. Blockers

None for the assigned additive scope.  Folding the guards into `Step` is not
blocked by a proof obligation; it is a larger shared-relation migration whose
exact downstream surface is §7.1.  Keeping the layer separate is the
scope-preserving choice required by the lane constraints.

## 11. Reproduction

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

# Build (shared lock, single Lean worker).
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.State \
    LnLean.Proofs.Channel.CommitmentDanceTargets \
    LnLean.Proofs.Channel.StateTransitionTargets

# Exact signature dump.
lake env lean /tmp/opencode/checks_dance.lean

# Axiom audit.
lake env lean /tmp/opencode/axioms_dance.lean

# Forbidden-construct scan.
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/CommitmentDanceTargets.lean

# Owned-file status.
git diff --numstat -- LnLean/Channel/State.lean
git status --short -- \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/CommitmentDanceTargets.lean \
  agents/reports/swarm6/S6-MODEL-DANCE.md
```

## 12. Line anchors

`LnLean/Channel/State.lean`

- additive section comment 458
- `DanceEvent` 484
- `DanceEvent.toProtocolEvent` 491
- `DanceOrdered` 498
- `commitmentGap` 504
- `CommitmentRevoked` 512
- `signRemoteCommitment` 517
- `revokeLocalCommitment` 523
- `DanceStep` 536
- `DanceStep.toStep` 548
- `DanceReachable` 559

`LnLean/Proofs/Channel/CommitmentDanceTargets.lean`

- successor projections 84–127
- guard extraction 131–174
- round window 177–229
- counter/revocation ordering 231–357
- ledger/reserve preservation 360–431
- compatibility bridges 434–471
- revocation-store view 475–511
- two-round witness 513–583
- retained unguarded-add counterexample 586–598
- dance counterexamples 600–651
