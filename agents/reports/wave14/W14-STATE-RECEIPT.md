# W14-STATE-RECEIPT — numbered, idempotent `commitment_signed` receipt adapter

**Lane:** `W14-STATE-RECEIPT` (Wave 14)
**Worktree:** `/home/ubuntu/ln-lean-waveh`
**Branch / base:** `wave-14/16` / `a331b71`
**Status:** green under the scoped module build; no `sorry`, `axiom`, `admit`,
`native_decide`, `unsafe`, or `@[implemented_by]`.

## 1. Scope

This lane implements R32 §4 T5 (G09 / `REV-03`) as an **additive model
adapter**, not a change to the wave-A transition relation.

`PeerState.receive` and `ChannelRecord.advanceReceived` are untouched.  The
existing record-level refinement `advanceReceivedNumbered`
(`LnLean/Proofs/Protocol/ChannelReestablishProps.lean`) is reused, and
`duplicate_commitmentSigned_advances_twice` is retained and instantiated below.

The adapter takes the commitment number explicitly because BOLT 2's
`commitment_signed` message does not carry it on the wire in this model.  This
is documented as a model extension at the receipt boundary.

## 2. Owned files

Created (the only files written by this lane):

- `LnLean/Proofs/Wave14/NumberedReceipt.lean`
- `agents/reports/wave14/W14-STATE-RECEIPT.md` (this report)

No shared or other-lane file was edited.

## 3. Definitions and headline statements

Module namespace:
`LnLean.Proofs.Wave14.NumberedReceipt`.

### 3.1 Adapter

```lean
def receiveNumbered? (s : PeerState) (m : Msg) (commitmentNumber : Nat) :
    Option PeerState :=
  match s.transport with
  | .down => none
  | .up =>
      match m with
      | .commitmentSigned cm =>
          match findChannel s cm.channelId with
          | none => none
          | some c =>
              if commitmentNumber = c.reestablish.nextCommitmentNumber then
                some (updateChannel s cm.channelId
                  (fun _ => advanceReceivedNumbered c commitmentNumber))
              else
                some s
      | _ => receive s m
```

Behavioral boundary: only the `.commitmentSigned` branch is numbered.  Every
other message is exactly the old `receive`.  A duplicate or wrong/future
number returns the peer state literally unchanged (`some s`), not `none`.

### 3.2 Headline theorems

```lean
theorem receiveNumbered?_commitmentSigned_eq
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) :
    receiveNumbered? s (.commitmentSigned cm) k =
      match s.transport with
      | .down => none
      | .up =>
          match findChannel s cm.channelId with
          | none => none
          | some c =>
              if k = c.reestablish.nextCommitmentNumber then
                some (updateChannel s cm.channelId
                  (fun _ => advanceReceivedNumbered c k))
              else
                some s
```

```lean
theorem advanceReceivedNumbered_channelId (c : ChannelRecord) (k : Nat) :
    (advanceReceivedNumbered c k).channelId = c.channelId

theorem advanceReceivedNumbered_fresh (c : ChannelRecord) (k : Nat)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    (advanceReceivedNumbered c k).reestablish.nextCommitmentNumber = k + 1

theorem advanceReceivedNumbered_wrong (c : ChannelRecord) (k : Nat)
    (hk : k ≠ c.reestablish.nextCommitmentNumber) :
    advanceReceivedNumbered c k = c
```

```lean
theorem advanceReceivedNumbered_replay (c : ChannelRecord) (k : Nat)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    (advanceReceivedNumbered (advanceReceivedNumbered c k) k)
        .reestablish.nextCommitmentNumber
      = c.reestablish.nextCommitmentNumber + 1
```

```lean
theorem receiveNumbered_some_of_expected
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k =
      some (updateChannel s cm.channelId
        (fun _ => advanceReceivedNumbered c k))
```

**Fresh case.**

```lean
theorem receiveNumbered_fresh_advances
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    ∃ c', findChannel s' cm.channelId = some c' ∧
      c'.reestablish.nextCommitmentNumber = k + 1
```

**Wrong-number case (literal state no-op).**

```lean
theorem receiveNumbered_wrongNumber_noop
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k ≠ c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k = some s
```

**Idempotence.**

```lean
theorem receiveNumbered_idempotent
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s'
```

**Duplicate/replay case (counter stays `k+1`, not `k+2`).**

```lean
theorem receiveNumbered_duplicate_noop
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s' ∧
      (∀ c', findChannel s' cm.channelId = some c' →
        c'.reestablish.nextCommitmentNumber = k + 1)

theorem replay_does_not_double_advance
    (s s' : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber)
    (h : receiveNumbered? s (.commitmentSigned cm) k = some s') :
    receiveNumbered? s' (.commitmentSigned cm) k = some s' ∧
      (∀ c', findChannel s' cm.channelId = some c' →
        c'.reestablish.nextCommitmentNumber =
          c.reestablish.nextCommitmentNumber + 1)
```

**Agreement with the old path on a fresh number.**

```lean
theorem receiveNumbered_eq_receive_of_expected
    (s : PeerState) (cm : CommitmentSigned) (k : Nat) (c : ChannelRecord)
    (ht : s.transport = .up)
    (hf : findChannel s cm.channelId = some c)
    (hk : k = c.reestablish.nextCommitmentNumber) :
    receiveNumbered? s (.commitmentSigned cm) k =
      receive s (.commitmentSigned cm)
```

**Retention of the old counterexample.**

```lean
theorem old_path_still_double_advances :
    ((sampleRecord.advanceReceived (.commitmentSigned sampleCommitmentSigned))
        .advanceReceived (.commitmentSigned sampleCommitmentSigned))
      .reestablish.nextCommitmentNumber = 2
```

This instantiates the retained
`LnLean.Proofs.Protocol.duplicate_commitmentSigned_advances_twice`; it does not
replace or weaken it.

## 4. Non-vacuity witnesses

Concrete carrier:

```lean
def sampleChannelId : ChannelId := ⟨ByteArray.empty⟩

def sampleRecord : ChannelRecord where
  channelId := sampleChannelId
  reestablish := ReestablishFields.initial   -- nextCommitmentNumber = 0

def samplePeer : PeerState where
  identity := ⟨ByteArray.empty⟩
  transport := .up
  handshake := HandshakeState.initial
  channels := [sampleRecord]

def sampleCommitmentSigned : CommitmentSigned where
  channelId := sampleChannelId
  signature := ⟨ByteArray.empty⟩
  htlcSignatures := []
```

The three required branches are exhibited by:

- `samplePeer_fresh_witness`: number `0` is accepted, the addressed counter
  becomes `1`.
- `samplePeer_duplicate_witness`: the second receipt with number `0` returns
  the same state, and the counter remains `1` (not `2`).
- `samplePeer_wrongNumber_witness`: number `1` is not the expected `0`, so
  `receiveNumbered? samplePeer ... 1 = some samplePeer` literally.
- `old_path_still_double_advances`: the retained unnumbered path advances the
  same concrete record from `0` to `2`.

`samplePeer_findChannel` is proved explicitly because `ChannelId` derives
`BEq` rather than `DecidableEq`.

## 5. Build

Command (shared lock, exact module only):

```sh
cd /home/ubuntu/ln-lean-waveh
export PATH=/dev/shm/btc/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 3600 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Wave14.NumberedReceipt
```

Result:

```
ℹ [17/17] Built LnLean.Proofs.Wave14.NumberedReceipt (810ms)
Build completed successfully (17 jobs).
```

No bare `lake build`, full gate, or network command was run.

## 6. `#print axioms` output

The commands are in the module at `LnLean/Proofs/Wave14/NumberedReceipt.lean:468-479`.
Build transcript (line wrapping from the logger is normalized):

```
receiveNumbered_idempotent:
  [propext, Quot.sound]
replay_does_not_double_advance:
  [propext, Quot.sound]
receiveNumbered_some_of_expected:
  [propext]
receiveNumbered_fresh_advances:
  [propext, Quot.sound]
receiveNumbered_duplicate_noop:
  [propext, Quot.sound]
receiveNumbered_wrongNumber_noop:
  [propext]
receiveNumbered_eq_receive_of_expected:
  [propext]
advanceReceivedNumbered_replay:
  [propext, Classical.choice, Quot.sound]
samplePeer_fresh_witness:
  [propext, Classical.choice, Quot.sound]
samplePeer_duplicate_witness:
  [propext, Classical.choice, Quot.sound]
samplePeer_wrongNumber_witness:
  [propext, Classical.choice, Quot.sound]
old_path_still_double_advances:
  [propext]
```

Only the permitted axioms `propext`, `Quot.sound`, and `Classical.choice`
appear.

## 7. Review gap closed / narrowed

**Closed at the model-adapter level (R32 §4 T5, §5.2, §6.2; G09 / `REV-03`).**

- A successful fresh numbered `commitment_signed` receipt advances the
  addressed channel exactly once.
- A duplicate number is a literal state no-op and is idempotent.
- A wrong/future number is a literal state no-op.
- Replay gives `+1`, while the retained unnumbered path still gives `+2`;
  both behaviors are now named and mechanically distinguished.
- On the expected number, the numbered adapter agrees with the old
  `receive` (`receiveNumbered_eq_receive_of_expected`), so the addition does
  not silently change the fresh path.

**What remains external or narrow.**

- **The wire does not carry the commitment number.**  The number is a
  caller-supplied model parameter.  No theorem claims BOLT 2 wire bytes carry
  it, and no theorem proves the caller supplies the correct number.
- **No error/fail-channel result.**  A wrong/future number is a no-op, not a
  rejection; `PeerState` has no channel-failure phase.
- **Only `commitment_signed` is numbered.**  Handshake replay and other
  message kinds delegate to `receive`; idempotence is not claimed for them.
- **No LDK/implementation conformance claim.**  The adapter is a Lean model
  boundary, not a projection of `lightning`'s internal commitment dance.
- **Identifier uniqueness is inherited, not proved.**  `updateChannel` maps
  every matching channel id; duplicate ids in a `PeerState` are not ruled out.
- **The old unnumbered path remains the wave-A transition.**  This lane adds
  a consumer; it does not rewire `receive`, and it does not delete or weaken
  `duplicate_commitmentSigned_advances_twice`.
- No persistence, event log, or cross-process duplicate suppression is
  modeled.

## 8. Shared-file changes for the integrator (stated, not applied)

The lane deliberately did not edit shared files.  The integrator should:

1. **Root import / regeneration.**  Run `scripts/regen-root.sh` (or add the
   generated root import for
   `LnLean.Proofs.Wave14.NumberedReceipt`) so the module is part of the full
   build.
2. **Axiom audit.**  If these declarations are to be in the audited surface,
   add their `#print axioms` lines to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean` and their names to
   `auditedTheorems`.  Suggested names: `receiveNumbered_idempotent`,
   `replay_does_not_double_advance`, `receiveNumbered_fresh_advances`,
   `receiveNumbered_duplicate_noop`, `receiveNumbered_wrongNumber_noop`,
   `receiveNumbered_eq_receive_of_expected`, `advanceReceivedNumbered_replay`,
   and `old_path_still_double_advances`.
3. **`docs/OPEN-ISSUES.md` `REV-03` wording.**  Add that the additive
   numbered adapter and its idempotence/fresh/duplicate/wrong-number theorems
   now exist in `LnLean/Proofs/Wave14/NumberedReceipt.lean`, while the wire
   still does not carry the number and `receive`/`advanceReceived` are
   unchanged.  Do not mark the whole replay issue closed if the old path is
   still the production consumer.
4. **Catalog / traceability (optional policy decision).**  This lane does not
   add a new obligation row.  If the project wants the adapter in the
   catalog, add a row or amend the `REV-03` evidence; if declaration-level
   traceability is maintained, index the headline names in
   `docs/THEOREM-INDEX.md` / `docs/TRACEABILITY.md`.
5. No change to `LnLean/Proofs/Protocol/ChannelReestablishProps.lean` is
   needed: the retained record lemma and counterexample remain exactly as
   they were.

## 9. Ownership confirmation

`git status --short` for this worktree shows only untracked lane artifacts
(`LnLean/Proofs/Wave14/`, `agents/reports/wave14/`, and the pre-existing
`agents/swarm/WAVE-14.md`).  No tracked shared file, existing Lean module,
script, docs file, or other lane's report was modified.  No Git write command
was run.
