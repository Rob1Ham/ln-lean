# S7-MODEL-FOLD — folding `UpdateStep` / `DanceStep` into the `ProtocolEvent` / `Step` fold

**Lane:** `S7-MODEL-FOLD` (`MODEL-02`, `MODEL-03`).
**Repository:** `/home/ubuntu/ln-lean-repair`.
**Branch / base:** `repair/integrated` at `3180581` (wave-7 launch).
**Verdict:** complete for the faithful scope.  The literal fold of the dance
guards into `Step` is **refuted by the existing counterexamples** (they are the
mechanized model-gap theorems, not scope notes), and a literal
`update_add_htlc` constructor would make the balance/HTLC preservation lemmas
used by `LiquidityProps`, `F03`, `D14`, and `LivenessDelivery` false.  This lane
therefore implements the strongest true form:

* the fold is realized as the new **guarded subrelation** `GuardedStep`
  (`Step` with the two round constructors guarded), which is exactly `Step` on
  every non-round message;
* the wave-6 dance is proved to be **exactly** the round fragment of that fold
  (`DanceStep c e c' ↔ GuardedStep c e.toProtocolEvent c'`);
* the single folded update relation `GuardedUpdateStep` is proved to be a
  subrelation of `UpdateStep`, so every wave-5 ledger/reserve theorem applies
  unchanged, while the **round window becomes an invariant** of folded traces;
* the impossibility of the two literal folds is itself mechanized, and every
  counterexample is retained and re-exported;
* exact downstream migration patches are recorded in §8 for the parent.

- Lane files:
  - `LnLean/Channel/State.lean` — additive section at lines 567–649
    (`GuardedStep`, `GuardedReachable`, `GuardedUpdateStep`,
    `GuardedUpdateReachable`); `git diff --numstat` reports `83  1` (the one
    deletion is the replaced module-docstring bullet).
  - `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean` — new, 779 lines.
  - `agents/reports/swarm7/S7-MODEL-FOLD.md` — this report.
- Not modified: `LnLean/Proofs/Liveness.lean`, `LnLean/Proofs/WaveD/D14.lean`,
  `LnLean/Proofs/Channel/StateMachineProps.lean`, `LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`,
  `scripts/check-final.py`, shared docs/catalog, other lanes' files,
  `vendor/**`.  No Git write command was run.  Other modified/untracked files
  visible in `git status` belong to concurrent lanes and were left untouched.

## 1. Result in one paragraph

Wave 5 added the HTLC update messages as the additive `UpdateStep` relation;
wave 6 added the ordered `commitment_signed` / `revoke_and_ack` round as
`DanceStep`.  This lane supplies the fold in the only form that keeps the tree
sound.  `GuardedStep` is `Step` with the two commitment-round constructors
replaced by their BOLT 2 ordered forms and every other constructor copied
verbatim (`GuardedStep.ofStep`).  The exact characterization
`guardedStep_iff_step_and_guards` says a guarded step is a `Step` whose
`commitment_signed` source is idle and whose `revoke_and_ack` source has exactly
one signature outstanding, and `guardedStep_ofStep_iff` says the two relations
agree on every non-round message.  The wave-6 dance is proved to be exactly the
round fragment of the fold (`danceStep_iff_guardedStep`), and the single folded
update relation `GuardedUpdateStep` (guarded lifecycle plus the three HTLC
messages) is a subrelation of `UpdateStep` (`guardedUpdateStep_toUpdateStep`),
so all wave-5 conservation/reserve theorems apply verbatim.  The payoff is a new
invariant: along any folded update trace starting `DanceOrdered`, every state
stays `DanceOrdered` and neither current commitment is revoked — an invariant
the unguarded `UpdateStep` cannot have, because its `lifecycle` constructor
embeds all of `Step`.  Two mechanized no-go results explain why the guards
cannot simply be added to `Step`: `literal_round_fold_refuted` /
`literal_revoke_fold_refuted` (the wave-6 and reestablish counterexamples would
become false) and `fold_cannot_both_preserve_balance_and_carry_add` /
`…_htlcs_…` (no relation can both preserve the D14/Liquidity/F03 invariants and
carry an affordable add).  The build is green (21 jobs) and the axiom surface is
only `propext`, `Quot.sound`, and `Classical.choice`.

## 2. What is mechanized

### 2.1 The folded relations in `State.lean`

```lean
inductive GuardedStep : Channel → ProtocolEvent → Channel → Prop where
  | ofStep {c c' : Channel} {e : ProtocolEvent} (h : Step c e c')
      (hcs : e ≠ ProtocolEvent.commitmentSigned)
      (hra : e ≠ ProtocolEvent.revokeAndAck) : GuardedStep c e c'
  | commitmentSigned (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
      GuardedStep c ProtocolEvent.commitmentSigned (signRemoteCommitment c)
  | revokeAndAck (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
      GuardedStep c ProtocolEvent.revokeAndAck (revokeLocalCommitment c)

inductive GuardedReachable : Channel → Channel → Prop
inductive GuardedUpdateStep (hashFn : ByteArray → ByteArray) :
    Channel → UpdateEvent → Channel → Prop   -- lifecycle + 3 HTLC constructors
inductive GuardedUpdateReachable (hashFn : ByteArray → ByteArray) :
    Channel → Channel → Prop
```

`GuardedStep` adds no message vocabulary: both guarded events already exist in
`ProtocolEvent`, and the targets are the wave-6 successors
`signRemoteCommitment` / `revokeLocalCommitment`.  `GuardedUpdateStep` adds no
event either: `UpdateEvent` already contains `lifecycle` plus the three HTLC
payloads.

### 2.2 Exact characterization (the fold theorem)

```lean
theorem guardedStep_iff_step_and_guards {c c' : Channel} {e : ProtocolEvent} :
    GuardedStep c e c' ↔
      Step c e c' ∧
        (e = ProtocolEvent.commitmentSigned →
          c.remoteCommitmentNumber = c.localCommitmentNumber) ∧
        (e = ProtocolEvent.revokeAndAck →
          c.remoteCommitmentNumber = c.localCommitmentNumber + 1)
```

This is an **iff**, not an implication: the fold is *exactly* the guarded
fragment of the existing lifecycle relation.  Two corollaries make it usable:

* `guardedStep_ofStep_iff (hcs) (hra) : GuardedStep c e c' ↔ Step c e c'` — on
  any non-round message the fold is conservative;
* `guardedStep_toStep : GuardedStep c e c' → Step c e c'` — the fold is a
  subrelation, so no existing `Step` theorem is weakened.

The fold is also deterministic (`guardedStep_deterministic`), inherits the
balance/HTLC/funding invariance of `Step` (`guardedStep_balance_eq`,
`guardedStep_htlcs_eq`, `guardedStep_fundingValue_eq`), and inherits E37 ledger
and reserve preservation (`guardedStep_preserves_ledger`,
`guardedStep_preserves_reserve`).

### 2.3 `DanceStep` is exactly the round fragment of the fold

```lean
theorem danceStep_iff_guardedStep {c c' : Channel} {e : DanceEvent} :
    DanceStep c e c' ↔ GuardedStep c e.toProtocolEvent c'
theorem guardedStep_commitmentSigned_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.commitmentSigned c' ↔
      DanceStep c DanceEvent.commitmentSigned c'
theorem guardedStep_revokeAndAck_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.revokeAndAck c' ↔
      DanceStep c DanceEvent.revokeAndAck c'
```

So the wave-6 layer is not a second semantics: it is the two-event fragment of
the fold, and conversely the fold's round fragment is the dance.  The guards
are extractable (`guardedStep_commitmentSigned_requires_idle`,
`guardedStep_revokeAndAck_requires_pending`) and load-bearing
(`no_guarded_commitmentSigned_with_round_in_flight`,
`no_guarded_revokeAndAck_without_commitmentSigned`).

### 2.4 The folded update relation and the new invariant

`GuardedUpdateStep` is the single folded update relation:

```lean
theorem guardedUpdateStep_lifecycle_iff {hashFn} {c c'} {e : ProtocolEvent} :
    GuardedUpdateStep hashFn c (.lifecycle e) c' ↔ GuardedStep c e c'
theorem guardedUpdateStep_toUpdateStep {hashFn} {c c'} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') : UpdateStep hashFn c e c'
```

Because it is a subrelation of `UpdateStep`, all wave-5 results transport
unchanged (`guardedUpdateStep_preserves_ledger`,
`guardedUpdateStep_preserves_reserve`, `guardedUpdateStep_add_affordable`,
`guardedUpdateStep_add_counters`,
`guardedUpdateReachable_preserves_ledger`,
`guardedUpdateReachable_preserves_reserve`).

The new content is the round-window invariant.  Every HTLC successor leaves
both commitment counters alone (six `[simp]` projections: `updateAddHtlc_*`,
`failHtlcAt_*`, `fulfillHtlcAt_*`), and every non-round lifecycle message does
too, so:

```lean
theorem guardedUpdateStep_preserves_ordered {hashFn} {c c'} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') (ho : DanceOrdered c) :
    DanceOrdered c'
theorem guardedUpdateReachable_preserves_ordered {hashFn} {a b : Channel}
    (h : GuardedUpdateReachable hashFn a b) : DanceOrdered a → DanceOrdered b
theorem guardedUpdateReachable_current_not_revoked {hashFn} {a b : Channel}
    (h : GuardedUpdateReachable hashFn a b) (ho : DanceOrdered a) (_hne : a ≠ b) :
    ¬ CommitmentRevoked b b.localCommitmentNumber ∧
      ¬ CommitmentRevoked b b.remoteCommitmentNumber
```

`UpdateStep` cannot carry this invariant: `UpdateStep.lifecycle` embeds every
`Step`, including the double-sign trace of wave 6.  This is the concrete value
of the fold.

### 2.5 The literal folds are refuted, not assumed away

```lean
theorem literal_round_fold_refuted :
    ¬ (∀ (c c' : Channel), Step c ProtocolEvent.commitmentSigned c' →
        c.remoteCommitmentNumber = c.localCommitmentNumber)
theorem literal_revoke_fold_refuted :
    ¬ (∀ (c c' : Channel), Step c ProtocolEvent.revokeAndAck c' →
        c.remoteCommitmentNumber = c.localCommitmentNumber + 1)
theorem fold_cannot_both_preserve_balance_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) :
    ¬ ((∀ {c c' : Channel} {e : UpdateEvent}, R c e c' →
          c'.balance = c.balance) ∧
        (∀ {c : Channel} {dir : Direction} {amount : Msat}
            {ph : PaymentHash} {cltv : Height},
          AffordableAdd c dir amount cltv →
            R c (.addHtlc dir amount ph cltv)
              (updateAddHtlc c dir amount ph cltv)))
theorem fold_cannot_both_preserve_htlcs_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) : …  -- same shape for htlcs
```

The witnesses are concrete: `step_commitmentSigned_unguarded_witness` (a
non-idle `commitment_signed` source), `affordable_add_changes_balance`, and
`affordable_add_changes_htlcs` (a 500-msat local add from
`E37.testChannel 1000 1000 2000 0 1 1000`).  These are the mechanized reason
the fold is a **subrelation**, not an edit of the `Step` constructors.

### 2.6 Non-vacuity and retained counterexamples

```lean
theorem guarded_two_rounds_witness : ∃ c c₁ c₂ c₃ c₄,
  GuardedReachable c c₄ ∧
    GuardedStep c .commitmentSigned c₁ ∧ GuardedStep c₁ .revokeAndAck c₂ ∧
      GuardedStep c₂ .commitmentSigned c₃ ∧ GuardedStep c₃ .revokeAndAck c₄ ∧
        DanceOrdered c₄ ∧ c₄.localCommitmentNumber = 2 ∧
          c₄.remoteCommitmentNumber = 2 ∧
            CommitmentRevoked c₄ 0 ∧ CommitmentRevoked c₄ 1
theorem guarded_update_add_witness : ∃ c c' e fee,
  GuardedUpdateStep (fun b => b) c e c' ∧ DanceOrdered c ∧ DanceOrdered c' ∧
    E37.ledgerValue c fee = c.fundingValue.val ∧
      E37.ledgerValue c' fee = c'.fundingValue.val
```

Both are closed existentials (no hypotheses), so the folded relations are
inhabited.  The retained counterexamples are

* `unguarded_add_ledger_counterexample_retained` (wave 5),
* `unguarded_double_commitmentSigned_breaks_ordering_retained` (wave 6),
* `unguarded_revokeAndAck_from_idle_breaks_ordering_retained` (wave 6),
* `unguarded_step_signs_revoked_commitment_retained` (wave 6),

and `guarded_no_double_commitmentSigned` proves the fold *excludes* the
double-sign interleaving, which is what makes the retained theorem a fact about
`Step` rather than a fact about the fold.

## 3. Exact signatures

Namespace: `LnLean.Proofs.Channel.ProtocolEventFoldTargets`.
Abbreviations below: `Channel` is `LnLean.Channel`, `E37` is
`LnLean.Proofs.WaveE.E37`, `ReserveInvariant` is
`LnLean.Proofs.Channel.ReserveInvariant`.  All signatures were emitted by
`#check` against the fully qualified names.

### 3.1 `Step` shadow lemmas

```lean
theorem step_balance_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.balance = c.balance
theorem step_htlcs_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.htlcs = c.htlcs
theorem step_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c'.fundingValue = c.fundingValue
```

### 3.2 Fold characterization

```lean
theorem guardedStep_toStep {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : Step c e c'
theorem guardedStep_iff_step_and_guards {c c' : Channel} {e : ProtocolEvent} :
    GuardedStep c e c' ↔
      Step c e c' ∧
        (e = ProtocolEvent.commitmentSigned →
          c.remoteCommitmentNumber = c.localCommitmentNumber) ∧
        (e = ProtocolEvent.revokeAndAck →
          c.remoteCommitmentNumber = c.localCommitmentNumber + 1)
theorem guardedStep_ofStep_iff {c c' : Channel} {e : ProtocolEvent}
    (hcs : e ≠ ProtocolEvent.commitmentSigned)
    (hra : e ≠ ProtocolEvent.revokeAndAck) :
    GuardedStep c e c' ↔ Step c e c'
theorem guardedStep_deterministic {c c₁ c₂ : Channel} {e : ProtocolEvent}
    (h₁ : GuardedStep c e c₁) (h₂ : GuardedStep c e c₂) : c₁ = c₂
theorem guardedStep_balance_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.balance = c.balance
theorem guardedStep_htlcs_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.htlcs = c.htlcs
theorem guardedStep_fundingValue_eq {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') : c'.fundingValue = c.fundingValue
theorem guardedStep_preserves_ledger {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') (fee : Msat)
    (hled : E37.ledgerValue c fee = c.fundingValue.val) :
    E37.ledgerValue c' fee = c'.fundingValue.val
theorem guardedStep_preserves_reserve {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') (hres : ReserveInvariant c) :
    ReserveInvariant c'
```

### 3.3 Dance = round fragment of the fold

```lean
theorem danceStep_toGuardedStep {c c' : Channel} {e : DanceEvent}
    (h : DanceStep c e c') : GuardedStep c e.toProtocolEvent c'
theorem danceStep_iff_guardedStep {c c' : Channel} {e : DanceEvent} :
    DanceStep c e c' ↔ GuardedStep c e.toProtocolEvent c'
theorem guardedStep_commitmentSigned_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.commitmentSigned c' ↔
      DanceStep c DanceEvent.commitmentSigned c'
theorem guardedStep_revokeAndAck_iff_danceStep {c c' : Channel} :
    GuardedStep c ProtocolEvent.revokeAndAck c' ↔
      DanceStep c DanceEvent.revokeAndAck c'
theorem guardedStep_commitmentSigned_requires_idle {c c' : Channel}
    (h : GuardedStep c ProtocolEvent.commitmentSigned c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber
theorem guardedStep_revokeAndAck_requires_pending {c c' : Channel}
    (h : GuardedStep c ProtocolEvent.revokeAndAck c') :
    c.remoteCommitmentNumber = c.localCommitmentNumber + 1
theorem no_guarded_commitmentSigned_with_round_in_flight {c c' : Channel}
    (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
    ¬ GuardedStep c ProtocolEvent.commitmentSigned c'
theorem no_guarded_revokeAndAck_without_commitmentSigned {c c' : Channel}
    (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
    ¬ GuardedStep c ProtocolEvent.revokeAndAck c'
```

### 3.4 Round window and folded lifecycle traces

```lean
theorem guardedStep_preserves_ordered {c c' : Channel} {e : ProtocolEvent}
    (h : GuardedStep c e c') (ho : DanceOrdered c) : DanceOrdered c'
theorem guardedReachable_preserves_ordered {a b : Channel}
    (h : GuardedReachable a b) : DanceOrdered a → DanceOrdered b
theorem danceReachable_toGuardedReachable {a b : Channel}
    (h : DanceReachable a b) : GuardedReachable a b
theorem guardedReachable_toReachable {a b : Channel}
    (h : GuardedReachable a b) : Reachable a b
theorem guardedReachable_trans {a b c : Channel}
    (hab : GuardedReachable a b) (hbc : GuardedReachable b c) :
    GuardedReachable a c
theorem guardedReachable_of_guardedStep {a b : Channel} {e : ProtocolEvent}
    (h : GuardedStep a e b) : GuardedReachable a b
theorem guardedReachable_preserves_ledger {a b : Channel}
    (h : GuardedReachable a b) (fee : Msat)
    (hled : E37.ledgerValue a fee = a.fundingValue.val) :
    E37.ledgerValue b fee = b.fundingValue.val
theorem guardedReachable_preserves_reserve {a b : Channel}
    (h : GuardedReachable a b) (hres : ReserveInvariant a) :
    ReserveInvariant b
```

### 3.5 Counter projections and the folded update relation

```lean
@[simp] theorem updateAddHtlc_localCommitmentNumber … : … = c.localCommitmentNumber
@[simp] theorem updateAddHtlc_remoteCommitmentNumber … : … = c.remoteCommitmentNumber
@[simp] theorem failHtlcAt_localCommitmentNumber (c : Channel) (i : Nat) : …
@[simp] theorem failHtlcAt_remoteCommitmentNumber (c : Channel) (i : Nat) : …
@[simp] theorem fulfillHtlcAt_localCommitmentNumber (c : Channel) (i : Nat) : …
@[simp] theorem fulfillHtlcAt_remoteCommitmentNumber (c : Channel) (i : Nat) : …

theorem guardedUpdateStep_toUpdateStep {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') : UpdateStep hashFn c e c'
theorem guardedUpdateStep_lifecycle_iff {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : ProtocolEvent} :
    GuardedUpdateStep hashFn c (.lifecycle e) c' ↔ GuardedStep c e c'
theorem guardedUpdateStep_deterministic {hashFn : ByteArray → ByteArray}
    {c c₁ c₂ : Channel} {e : UpdateEvent}
    (h₁ : GuardedUpdateStep hashFn c e c₁)
    (h₂ : GuardedUpdateStep hashFn c e c₂) : c₁ = c₂
theorem guardedUpdateStep_add_affordable {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height}
    (h : GuardedUpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    AffordableAdd c dir amount cltv
theorem guardedUpdateStep_add_counters {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {dir : Direction} {amount : Msat} {ph : PaymentHash}
    {cltv : Height}
    (h : GuardedUpdateStep hashFn c (.addHtlc dir amount ph cltv) c') :
    c'.localCommitmentNumber = c.localCommitmentNumber ∧
      c'.remoteCommitmentNumber = c.remoteCommitmentNumber
theorem guardedUpdateStep_preserves_ordered {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') (ho : DanceOrdered c) :
    DanceOrdered c'
theorem guardedUpdateStep_preserves_ledger {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') (fee : Msat)
    (hled : E37.ledgerValue c fee = c.fundingValue.val) :
    E37.ledgerValue c' fee = c'.fundingValue.val
theorem guardedUpdateStep_preserves_reserve {hashFn : ByteArray → ByteArray}
    {c c' : Channel} {e : UpdateEvent}
    (h : GuardedUpdateStep hashFn c e c') (hres : ReserveInvariant c) :
    ReserveInvariant c'
theorem guardedUpdateReachable_toUpdateReachable {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) :
    UpdateReachable hashFn a b
theorem guardedUpdateReachable_trans {hashFn : ByteArray → ByteArray}
    {a b c : Channel} (hab : GuardedUpdateReachable hashFn a b)
    (hbc : GuardedUpdateReachable hashFn b c) :
    GuardedUpdateReachable hashFn a c
theorem guardedUpdateReachable_preserves_ordered {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) :
    DanceOrdered a → DanceOrdered b
theorem guardedUpdateReachable_current_not_revoked {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b)
    (ho : DanceOrdered a) (_hne : a ≠ b) :
    ¬ CommitmentRevoked b b.localCommitmentNumber ∧
      ¬ CommitmentRevoked b b.remoteCommitmentNumber
theorem guardedUpdateReachable_preserves_ledger {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b) (fee : Msat)
    (hled : E37.ledgerValue a fee = a.fundingValue.val) :
    E37.ledgerValue b fee = b.fundingValue.val
theorem guardedUpdateReachable_preserves_reserve {hashFn : ByteArray → ByteArray}
    {a b : Channel} (h : GuardedUpdateReachable hashFn a b)
    (hres : ReserveInvariant a) : ReserveInvariant b
```

### 3.6 Non-vacuity, refutations, retained counterexamples

```lean
theorem guarded_two_rounds_witness : …      -- see §2.6
theorem guarded_update_add_witness : …      -- see §2.6
theorem step_commitmentSigned_unguarded_witness :
    ∃ (c c' : Channel), Step c ProtocolEvent.commitmentSigned c' ∧
      c.remoteCommitmentNumber ≠ c.localCommitmentNumber
theorem literal_round_fold_refuted : …
theorem literal_revoke_fold_refuted : …
theorem affordable_add_changes_balance :
    ∃ (c : Channel) (dir : Direction) (amount : Msat) (ph : PaymentHash)
        (cltv : Height),
      AffordableAdd c dir amount cltv ∧
        (updateAddHtlc c dir amount ph cltv).balance ≠ c.balance
theorem affordable_add_changes_htlcs : …    -- same shape for .htlcs
theorem fold_cannot_both_preserve_balance_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) : …
theorem fold_cannot_both_preserve_htlcs_and_carry_add
    (R : Channel → UpdateEvent → Channel → Prop) : …
theorem unguarded_add_ledger_counterexample_retained : …
theorem unguarded_double_commitmentSigned_breaks_ordering_retained : …
theorem unguarded_revokeAndAck_from_idle_breaks_ordering_retained : …
theorem unguarded_step_signs_revoked_commitment_retained : …
theorem guarded_no_double_commitmentSigned {c c₁ c₂ : Channel}
    (h₁ : GuardedStep c ProtocolEvent.commitmentSigned c₁)
    (h₂ : GuardedStep c₁ ProtocolEvent.commitmentSigned c₂) : False
```

## 4. Build

Built only the owned modules plus the two directly imported wave-5/6 proof
modules, under the shared lock, from `/home/ubuntu/ln-lean-repair`:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.State \
    LnLean.Proofs.Channel.ProtocolEventFoldTargets \
    LnLean.Proofs.Channel.StateTransitionTargets \
    LnLean.Proofs.Channel.CommitmentDanceTargets
```

Result:

```text
Build completed successfully (21 jobs).
```

RC 0, no warnings in the final build.  No full `lake build`, no
`collect-obligations.py`, no `collect-anchors.py`, no Git write.

## 5. Axiom audit

`#print axioms` was run over all 62 public theorems of the new module with a
scratch script outside the tree (`/tmp/opencode/checks_fold.lean`).  The
observed union is

```text
{propext, Quot.sound, Classical.choice}
```

with no `sorryAx`, no `Lean.ofReduceBool`, and no unapproved axiom.
21 theorems are axiom-free; 18 depend only on `propext`; 17 on
`{propext, Quot.sound}`; 6 on `{propext, Quot.sound, Classical.choice}` (all
six are the `…_preserves_ordered` / `current_not_revoked` / add witness family,
where `omega` uses classical decidability).  Selected rows:

```text
guardedStep_toStep                                     does not depend on any axioms
guardedStep_iff_step_and_guards                        does not depend on any axioms
guardedStep_ofStep_iff                                 does not depend on any axioms
danceStep_iff_guardedStep                              does not depend on any axioms
guardedStep_commitmentSigned_iff_danceStep             does not depend on any axioms
guardedStep_revokeAndAck_iff_danceStep                 does not depend on any axioms
guardedStep_preserves_ledger                           [propext, Quot.sound]
guardedStep_preserves_reserve                          [propext, Quot.sound]
guardedStep_preserves_ordered                          [propext, Classical.choice, Quot.sound]
guardedUpdateStep_toUpdateStep                         [propext]
guardedUpdateStep_lifecycle_iff                        [propext]
guardedUpdateStep_preserves_ordered                    [propext, Classical.choice, Quot.sound]
guardedUpdateReachable_preserves_ordered               [propext, Classical.choice, Quot.sound]
guardedUpdateReachable_current_not_revoked             [propext, Classical.choice, Quot.sound]
guarded_two_rounds_witness                             [propext, Quot.sound]
guarded_update_add_witness                             [propext, Classical.choice, Quot.sound]
literal_round_fold_refuted                             [propext]
literal_revoke_fold_refuted                            [propext]
affordable_add_changes_balance                         [propext, Quot.sound]
affordable_add_changes_htlcs                           [propext, Quot.sound]
fold_cannot_both_preserve_balance_and_carry_add        [propext, Quot.sound]
fold_cannot_both_preserve_htlcs_and_carry_add          [propext, Quot.sound]
unguarded_add_ledger_counterexample_retained           [propext, Quot.sound]
unguarded_double_commitmentSigned_breaks_ordering_retained  [propext]
unguarded_revokeAndAck_from_idle_breaks_ordering_retained   [propext]
unguarded_step_signs_revoked_commitment_retained            [propext]
guarded_no_double_commitmentSigned                     [propext, Classical.choice, Quot.sound]
```

## 6. Forbidden-construct scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean
```

Result: no matches (empty output, exit status 1).

`git diff --numstat -- LnLean/Channel/State.lean` reports `83  1`.  The one
deletion is the replaced module-docstring bullet at `State.lean:40`; no existing
declaration was removed or modified.  The new section is append-only at
`State.lean:567-649`.

## 7. Why the literal fold was not applied

The lane allowed either a literal fold with a coordinated migration **or** a
formal refinement.  The literal fold is not merely larger; it is *inconsistent
with retained counterexamples*:

1. **Dance guards in `Step`.**  `CommitmentDanceTargets.unguarded_double_commitmentSigned_breaks_ordering`
   (wave 6) and
   `ChannelReestablishProps.reachable_counters_inconsistent` (two consecutive
   `revoke_and_ack`s from idle) are theorems about the *unguarded* `Step`.  If
   `Step.commitmentSigned`/`Step.revokeAndAck` carried the dance guards, both
   would be **false**.  `literal_round_fold_refuted` and
   `literal_revoke_fold_refuted` are the mechanized refutations of the required
   guard statements.  Deleting or weakening those counterexamples is forbidden
   by the lane policy, and `ChannelReestablishProps` is outside the owned set.
2. **`update_add_htlc` in `Step`.**  `Step` is balance- and HTLC-preserving
   (`LiquidityProps.step_preserves_balance`,
   `D14.waveD_d14_step_balance`, `D14.waveD_d14_step_htlcs`,
   `F03.step_htlcs_eq`, `LivenessDelivery.step_htlcs_eq`, and the reserve
   lemmas).  A constructor carrying an affordable add necessarily changes both
   (`affordable_add_changes_balance`, `affordable_add_changes_htlcs`), so no
   relation can keep those statements and accept the add
   (`fold_cannot_both_preserve_balance_and_carry_add`,
   `…_htlcs_…`).  Repairing them requires restating every lemma with an
   event-exclusion hypothesis, which is a breaking API change across a dozen
   files.

The guarded subrelation is therefore the strongest true form: it gives the
dance ordering, the single folded vocabulary, the round-window invariant, and
complete conservativity, while preserving every counterexample.  The literal
patches are recorded below for the parent to apply as one coordinated change if
that trade-off is ever chosen.

## 8. Exact downstream migration patches (not applied)

### 8.1 Migration A — fold the dance guards into `Step`

This is mechanically possible but **blocked by §7.1**; it requires deleting two
retained counterexamples or restating them against a new unguarded relation.

**A.1 `LnLean/Channel/State.lean` (lines 102-110).**  Add the two guard
binders; keep the record-update targets so no declaration moves:

```lean
  | commitmentSigned (c : Channel) (h : c.phase = ChannelPhase.normal)
      (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
      Step c ProtocolEvent.commitmentSigned
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
  | revokeAndAck (c : Channel) (h : c.phase = ChannelPhase.normal)
      (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
      Step c ProtocolEvent.revokeAndAck
        { c with localCommitmentNumber := c.localCommitmentNumber + 1 }
```

**A.2 `LnLean/Proofs/Liveness.lean`.**

*`step?` (lines 143-150)* — replace the two branches:

```lean
  | .commitmentSigned =>
      if c.phase = ChannelPhase.normal then
        if c.remoteCommitmentNumber = c.localCommitmentNumber then
          some { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
        else none
      else none
  | .revokeAndAck =>
      if c.phase = ChannelPhase.normal then
        if c.remoteCommitmentNumber = c.localCommitmentNumber + 1 then
          some { c with localCommitmentNumber := c.localCommitmentNumber + 1 }
        else none
      else none
```

*`step?_sound` (lines 200-211)* — replace the two branches:

```lean
  | commitmentSigned =>
      by_cases hg : c.phase = ChannelPhase.normal
      · by_cases hidle : c.remoteCommitmentNumber = c.localCommitmentNumber
        · simp [step?, hg, hidle] at h
          cases h
          simpa [hidle] using Step.commitmentSigned c hg hidle
        · simp [step?, hg, hidle] at h
      · simp [step?, hg] at h
  | revokeAndAck =>
      by_cases hg : c.phase = ChannelPhase.normal
      · by_cases hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1
        · simp [step?, hg, hpending] at h
          cases h
          simpa [hpending] using Step.revokeAndAck c hg hpending
        · simp [step?, hg, hpending] at h
      · simp [step?, hg] at h
```

*`step?_complete` (lines 240-241)* — add the new binders:

```lean
  | commitmentSigned hg hidle => simp [step?, hg, hidle]
  | revokeAndAck hg hpending => simp [step?, hg, hpending]
```

*`step_event_of_awaitingLockin` (lines 331-332)* — add a wildcard:

```lean
  | commitmentSigned h _ => exact absurd (h.symm.trans hc) (by decide)
  | revokeAndAck h _ => exact absurd (h.symm.trans hc) (by decide)
```

`noLoss_shuttingDown_eventually_closed` uses `cases hs <;> simp_all` and
recompiles unchanged.

**A.3 `LnLean/Proofs/Channel/StateMachineProps.lean`.**

*`step_allowedPhaseTransition` (lines 156-161)* — add `_` binders:

```lean
  | commitmentSigned h _ => rw [h]; exact AllowedPhaseTransition.normal_normal
  | revokeAndAck h _ => rw [h]; exact AllowedPhaseTransition.normal_normal
```

*`normal_phase_is_relational` (lines 211-218)* — the current revoke witness is
idle, so it needs a source with `remote = local + 1`:

```lean
  refine ⟨witnessChannel .normal,
    { witnessChannel .normal with remoteCommitmentNumber := 1 },
    { witnessChannel .normal with
        localCommitmentNumber := 1, remoteCommitmentNumber := 1 },
    .commitmentSigned, .revokeAndAck, ?_, ?_, ?_⟩
  · decide
  · exact Step.commitmentSigned (witnessChannel .normal) rfl rfl
  · exact Step.revokeAndAck
      { witnessChannel .normal with remoteCommitmentNumber := 1 } rfl rfl
```

The other eleven `step_*` theorems use wildcard `cases h` and recompile.

**A.4 `LnLean/Proofs/WaveD/D14.lean`** — the two counterexamples stay true
(both demo channels have `local = remote = 0`); add the guard proof:

```lean
-- lines 638 and 641
ProtocolEvent.commitmentSigned, Step.commitmentSigned demoChannel rfl rfl, ?_⟩
((waveD_d14_step_reserve_iff (Step.commitmentSigned demoChannel rfl rfl)).1 h')
-- lines 652 and 655
Step.commitmentSigned demoExposedChannel rfl rfl, demoExposedChannel_not_exposure, ?_⟩
(waveD_d14_step_exposure (Step.commitmentSigned demoExposedChannel rfl rfl) demoPolicy)
```

**A.5 `LnLean/Proofs/Protocol/ChannelReestablishProps.lean`** — **blocker**.
`reachable_counters_inconsistent` (lines 527-540) becomes false.  There is no
faithful patch: it must either be deleted or restated for a separate unguarded
relation (`Step` before the fold).  Recommend keeping the current `Step`.

**A.6 `LnLean/Proofs/Channel/CommitmentDanceTargets.lean`** — the three
counterexamples (lines 604-650) become false; `DanceStep.toStep` only gains the
guard arguments:

```lean
  | commitmentSigned hphase hidle =>
      simpa [DanceEvent.toProtocolEvent, signRemoteCommitment] using
        Step.commitmentSigned c hphase hidle
  | revokeAndAck hphase hpending =>
      simpa [DanceEvent.toProtocolEvent, revokeLocalCommitment] using
        Step.revokeAndAck c hphase hpending
```

**A.7 `LnLean/Proofs/PhaseC3/PersistenceRecovery.lean`** — the two refinement
bridges gain the guards as hypotheses:

```lean
theorem applyMsg_commitmentSigned_refines_step (eff : HtlcEffect) (c : Channel)
    (r : ChannelRecord) (m : CommitmentSigned)
    (hphase : c.phase = ChannelPhase.normal)
    (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) : …
  ⟨{ c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 },
    Step.commitmentSigned c hphase hidle, rfl⟩

theorem applyMsg_revokeAndAck_refines_step (eff : HtlcEffect) (c : Channel)
    (r : ChannelRecord) (m : RevokeAndAck)
    (hphase : c.phase = ChannelPhase.normal)
    (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) : …
  ⟨{ c with localCommitmentNumber := c.localCommitmentNumber + 1 },
    Step.revokeAndAck c hphase hpending, rfl⟩
```

**A.8 `LnLean/Proofs/WaveD/D13.lean`** — the checked relation needs the idle
guard so that `_step` remains provable:

```lean
  | commitmentSigned (c : Channel) (cm : Commitment)
      (hphase : c.phase = ChannelPhase.normal)
      (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber)
      (hsufficient : waveD_d13_commitmentFeeSufficient r cm) :
      waveD_d13_FeeCheckedStep r c cm ProtocolEvent.commitmentSigned
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 } cm
```

Then:

```lean
  | commitmentSigned hphase hidle _ =>
      exact Step.commitmentSigned c hphase hidle
```

and `waveD_d13_feeCheckedStep_commitmentSigned_iff` (lines 450-465) gains
`c.remoteCommitmentNumber = c.localCommitmentNumber` in its RHS.  `lift`
(405-411) is unchanged; it inherits the revoke guard from `hstep`.

**A.9 `LnLean/Proofs/Channel/FeeTargets.lean`** — recompile after A.8; the six
D13-bridge declarations may need the idle condition threaded through the
`checkedCommitmentSigned` constructors.  The fee-gate statements themselves are
unchanged.

**A.10 Recompile-only files** (wildcard `cases h`, statements stay true):
`LnLean/Proofs/Payment/LiquidityProps.lean` (`step_preserves_balance`,
`step_preserves_fundingValue`, `step_preserves_meetsReserve`),
`LnLean/Proofs/ModelHardening/F03.lean` (`step_htlcs_eq`,
`step_preserves_ledgerBalanced`),
`LnLean/Proofs/WaveD/D14.lean` (all `step_*` except the two witnesses),
`LnLean/Proofs/PhaseC2/LivenessDelivery.lean`,
`LnLean/Channel/Laws.lean`, `LnLean/Proofs/Channel/ReserveProps.lean`,
`LnLean/Proofs/Channel/StateMachineProps.lean` (except A.3),
`LnLean/Proofs/Common.lean`.

### 8.2 Migration B — add an affordable `update_add_htlc` to `Step`

**Not faithful.**  Do not apply unless the D14/F03/Liquidity statements are
restated in the same patch.

Patch sketch:

```lean
-- State.lean
inductive ProtocolEvent where
  …
  | updateAddHtlc (direction : Direction) (amount : Msat)
      (paymentHash : PaymentHash) (cltvExpiry : Height)

inductive Step : Channel → ProtocolEvent → Channel → Prop where
  …
  | update_add_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
      (haff : AffordableAdd c dir amount cltv) :
      Step c (.updateAddHtlc dir amount ph cltv)
        (updateAddHtlc c dir amount ph cltv)
```

Then `Liveness.step?` gains the branch and `step?_sound`/`step?_complete` a
fourth block.  Every affected preservation lemma must gain an exclusion
hypothesis, for example:

```lean
theorem step_preserves_balance {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c')
    (hne : ∀ (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height),
      e ≠ ProtocolEvent.updateAddHtlc dir amount ph cltv) :
    c'.balance = c.balance
```

and similarly for `step_htlcs_eq` / `step_preserves_ledgerBalanced` /
`waveD_d14_step_exposure` / `LivenessDelivery.step_htlcs_eq` /
`runPrefix_htlcs` / the `ReserveProps` balance and reserve lemmas.  Every
consumer must discharge `hne` (or switch to `UpdateStep`).  The mechanized
witnesses `affordable_add_changes_balance` and `affordable_add_changes_htlcs`
show that the unguarded versions are simply false, and
`fold_cannot_both_preserve_balance_and_carry_add` shows there is no clever
repair.

**Recommendation.**  Keep `Step` as the lifecycle fold and expose
`GuardedUpdateStep` as the single consumer-facing relation.  This is the
"coordinated migration" with zero downstream breakage: existing `Step`
consumers keep their theorems, and new HTLC/round consumers use the fold.

## 9. Integration steps (parent-owned; not performed here)

1. **Root import.**  Do not hand-edit `LnLean.lean`; run
   `scripts/regen-root.sh` so that
   `import LnLean.Proofs.Channel.ProtocolEventFoldTargets` appears in the root.
2. **Axiom audit.**  Add
   `LnLean.Proofs.Channel.ProtocolEventFoldTargets` to the audited module list
   in `AxiomAudit.lean` (or the equivalent script configuration).  Expected
   dependencies are subsets of `{propext, Quot.sound, Classical.choice}`.
3. **Catalog.**  Suggested `MODEL-02` / `MODEL-03` replacement rows:

   ```text
   | `MODEL-02` | P2 | addressed (guarded fold) | HTLC messages and the commitment round are folded into one guarded subrelation | `LnLean.Channel.GuardedUpdateStep` embeds the guarded lifecycle relation and the three HTLC messages; `guardedUpdateStep_toUpdateStep` keeps every wave-5 ledger/reserve theorem, `guardedUpdateStep_lifecycle_iff` fixes the lifecycle fragment, and `guardedUpdateReachable_preserves_ordered` adds the round-window invariant. A literal `Step.update_add_htlc` constructor is refuted by `fold_cannot_both_preserve_balance_and_carry_add`; the exact migration patch is in `agents/reports/swarm7/S7-MODEL-FOLD.md` §8.2. |
   | `MODEL-03` | P2 | addressed (guarded fold) | The ordered commitment round is the guarded fragment of the lifecycle fold | `LnLean.Channel.GuardedStep` replaces the two unguarded round constructors; `guardedStep_iff_step_and_guards` is the exact characterization, `danceStep_iff_guardedStep` proves `DanceStep` is exactly its round fragment, and `literal_round_fold_refuted` / `literal_revoke_fold_refuted` prove the literal `Step` fold is inconsistent with the retained wave-6 and reestablish counterexamples. |
   ```

4. **Traceability.**  Add rows mapping `MODEL-02` / `MODEL-03` to
   `LnLean.Channel.GuardedStep`,
   `LnLean.Channel.GuardedUpdateStep`,
   `ProtocolEventFoldTargets.guardedStep_iff_step_and_guards`,
   `danceStep_iff_guardedStep`,
   `guardedUpdateReachable_preserves_ordered`,
   `guardedUpdateReachable_current_not_revoked`,
   `literal_round_fold_refuted`, and
   `fold_cannot_both_preserve_balance_and_carry_add`.
5. **Theorem index / docs.**  Add one sentence: `Step` is the unguarded
   lifecycle relation; `GuardedStep` is the guarded lifecycle fold;
   `UpdateStep` is the HTLC layer; `GuardedUpdateStep` is the single folded
   relation used by new consumers; `DanceStep` is the round fragment of
   `GuardedStep`.
6. **Full gate.**  Run the full build and all gates only after the root import
   and audit lists are regenerated in the parent worktree.

## 10. Scope caveats

- **The fold is a subrelation, not a new message vocabulary.**  `GuardedStep`
  and `GuardedUpdateStep` do not add constructors to `ProtocolEvent` or
  `UpdateEvent`; they restrict the existing ones.  A consumer that needs the
  unguarded relation (for the counterexamples) still uses `Step` /
  `UpdateStep`.
- **Pending-update queue.**  No relation in this lane models which pending
  HTLC updates a `commitment_signed` commits.  The fold composes message
  effects, not the BOLT 2 queue or the `channel_reestablish` replay rules.
- **Signatures and per-commitment material.**  `commitment_signed` /
  `revoke_and_ack` payloads, per-commitment points, and the wire format remain
  abstract (`LnLean.Protocol.Messages` untouched).
- **BOLT 3 `2^48` bound.**  `Channel` does not enforce
  `localCommitmentNumber ≤ 2^48`; the wave-6 `danceStore` bound remains the
  only statement, and no wrap-around is modelled.
- **Revocation abstraction.**  `CommitmentRevoked` is the local watermark
  `i < localCommitmentNumber`; the fold inherits it and does not model the
  shachain.
- **One round at a time.**  `GuardedStep` allows at most one outstanding
  `commitment_signed` (`remote = local + 1`).  Batched or pipelined rounds are
  not modelled.
- **`GuardedStep.ofStep` carries two disequality proofs.**  Consumers doing
  `cases` on a guarded step see `hcs : e ≠ commitmentSigned` and
  `hra : e ≠ revokeAndAck`; `guardedStep_iff_step_and_guards` is usually the
  easier interface.
- **No `GuardedUpdateReachable → Reachable`.**  The folded update relation
  contains the three HTLC transitions, which are not `Step` transitions; only
  the lifecycle fragment (`GuardedStep`) embeds into `Reachable`.  This is a
  theorem-shaped absence, not an omission: the analogous implication is false.
- **Classical choice.**  Six invariant theorems use `omega` and therefore
  `Classical.choice`; this is within the allowed axiom set and matches the
  wave-6 dance module.

## 11. Blockers

The only blocker is the one described in §7: the literal fold of the dance
guards into `Step` requires making
`CommitmentDanceTargets.unguarded_double_commitmentSigned_breaks_ordering` and
`ChannelReestablishProps.reachable_counters_inconsistent` false, and the
literal add constructor requires making the balance/HTLC invariance lemmas of
`D14`, `F03`, `LiquidityProps`, and `LivenessDelivery` false.  Both conflict
with the lane rule "preserve all counterexamples".  No proof obligation is
blocked; the guarded fold plus the exact patches in §8 is the complete faithful
deliverable.

## 12. Reproduction

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH

# Build (shared lock, single Lean worker).
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Channel.State \
    LnLean.Proofs.Channel.ProtocolEventFoldTargets \
    LnLean.Proofs.Channel.StateTransitionTargets \
    LnLean.Proofs.Channel.CommitmentDanceTargets

# Exact signature dump and axiom audit (scratch file outside the tree).
lake env lean /tmp/opencode/checks_fold.lean

# Forbidden-construct scan.
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean

# Owned-file status.
git diff --numstat -- LnLean/Channel/State.lean
git status --short -- \
  LnLean/Channel/State.lean \
  LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean \
  agents/reports/swarm7/S7-MODEL-FOLD.md
```

## 13. Line anchors

`LnLean/Channel/State.lean`

- folded-layer section comment 567
- `GuardedStep` 591
- `GuardedReachable` 607
- `GuardedUpdateStep` 615
- `GuardedUpdateReachable` 639

`LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean`

- `Step` shadow lemmas 84
- fold characterization 105 (`guardedStep_iff_step_and_guards` 124)
- dance = round fragment 205 (`danceStep_iff_guardedStep` 249)
- round window 293
- counter projections 371
- folded update relation 407 (`guardedUpdateStep_preserves_ordered` 467)
- non-vacuity 551 (`guarded_two_rounds_witness` 559,
  `guarded_update_add_witness` 580)
- refutations 610 (`literal_round_fold_refuted` 634,
  `fold_cannot_both_preserve_balance_and_carry_add` 696)
- retained counterexamples 725

## 14. Summary for the parent

- **Verdict:** the literal fold is impossible without falsifying retained
  counterexamples; the guarded fold `GuardedStep` / `GuardedUpdateStep` is the
  strongest true form, and it is proved to be exactly the guarded fragment of
  `Step` and exactly the dance on the two round messages.
- **New model decls (`LnLean/Channel/State.lean`, append-only):**
  `GuardedStep`, `GuardedReachable`, `GuardedUpdateStep`,
  `GuardedUpdateReachable` (83 lines added, 1 docstring line replaced).
- **New proofs:** 62 theorems in
  `LnLean/Proofs/Channel/ProtocolEventFoldTargets.lean` (779 lines).
- **Headline results:** `guardedStep_iff_step_and_guards`,
  `danceStep_iff_guardedStep`, `guardedUpdateStep_toUpdateStep`,
  `guardedUpdateReachable_preserves_ordered`,
  `guardedUpdateReachable_current_not_revoked`,
  `literal_round_fold_refuted`, `literal_revoke_fold_refuted`,
  `fold_cannot_both_preserve_balance_and_carry_add`.
- **Build:** `Build completed successfully (21 jobs).` RC 0.
- **Axioms:** union `{propext, Quot.sound, Classical.choice}`; no `sorryAx`,
  no unapproved axiom.
- **Counterexamples:** all four wave-5/6 counterexamples retained and
  re-exported; the fold is proved to exclude the double-sign trace.
- **Integration:** regenerate the root import, add the module to the axiom
  audit, update the `MODEL-02` / `MODEL-03` catalog rows and traceability,
  add the one-sentence theorem-index note.  Exact literal-migration patches
  (A.1-A.10, B) are in §8; do not apply A or B without resolving the
  counterexample conflict.
- **Blockers:** none for the delivered scope; the literal fold is blocked by
  `CommitmentDanceTargets.unguarded_double_commitmentSigned_breaks_ordering`,
  `ChannelReestablishProps.reachable_counters_inconsistent`, and the
  D14/F03/Liquidity balance/HTLC invariance lemmas.
