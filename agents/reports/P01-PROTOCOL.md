# P01-PROTOCOL — protocol rows LN-PR-001 … LN-PR-006

Lane: P01-PROTOCOL (proof lane)
Repo: `/home/ubuntu/ln-lean-repair`
Branch: `repair/integrated` (HEAD `2586bf5`)
Toolchain: `leanprover/lean4:v4.35.0`, Lake `5.0.0-src+eb6cafb`
Owned paths: `LnLean/Protocol/Handshake.lean`, `LnLean/Protocol/Peer.lean`,
`agents/reports/P01-PROTOCOL.md`.
Files actually changed: **`LnLean/Protocol/Peer.lean`** and this report only.

## 0. Verdict summary

| Row | Catalog target | Exact target exists? | Verdict | Promotion-ready? |
|---|---|---|---|---|
| LN-PR-001 | `LnLean.Protocol.Handshake.open_bounds` | no | faithful acceptor model exists in **D17** under a different name | **no** at this target; retarget to D17 |
| LN-PR-003 | `LnLean.Protocol.Handshake.funding_signed_valid` | no | wave-A message has no funding tx/key and only length-checks signatures; faithful crypto model in **E19** | **no** at this target; retarget to E19 |
| LN-PR-004 | `LnLean.Protocol.Messages.commitment_signed_covers` | no | wire record has no HTLC set/fee/commitment; the unconditional statement is false; faithful conditional model in **E20** | **no** at this target; retarget to E20 |
| LN-PR-005 | `LnLean.Protocol.Peer.reestablish_no_rollback` | **yes** | **proved** (kernel-checked, no `sorry`, no `axiom`) | **yes**, subject to the integrator flipping the catalog status |
| LN-PR-006 | `LnLean.Protocol.Handshake.feature_intersection` | no | `init` features are opaque `ByteArray`s; feature-vector model is in **FeaturesProps / FeatureClosure**, and the wording “intersection of supported features” needs qualification | **no** at this target; retarget + reword |

No fake exact target was added for the four blocked rows. No other Lean file was
edited.

## 1. Build evidence

All Lean invocations ran one at a time under
`flock -w 1800 /tmp/opencode/btc-lean/build.lock` with `LEAN_NUM_THREADS=1`.

| # | Command | RC |
|---|---|---|
| 1 | `lake env lean LnLean/Protocol/Peer.lean` | **0** |
| 2 | `lake build LnLean.Protocol.Peer LnLean.Protocol.Handshake` | **0** (8 jobs; `Peer` rebuilt) |
| 3 | `lake env lean /tmp/opencode/btc-lean/CheckP01.lean` | **0** |
| 4 | `python3 scripts/check-catalog.py --allow-planned` | **0** |

Note on the requested build line: this Lake (5.0.0-src+eb6cafb) rejects
`lake build -j1 …` with `error: unknown short option '-j'`. The equivalent
serial invocation is `LEAN_NUM_THREADS=1 lake build LnLean.Protocol.Peer
LnLean.Protocol.Handshake` (command 2 above), which is what was run.

`#check` output (scratch file `/tmp/opencode/btc-lean/CheckP01.lean`, outside
the tree):

```
Protocol.Peer.reestablish_no_rollback :
  (∀ (s : Protocol.PeerState) (channelId : ChannelId) (kind : Protocol.MsgKind)
      (c : Protocol.ChannelRecord),
      Protocol.findChannel s channelId = some c →
        Protocol.resend s channelId kind = c.lastSent kind) ∧
  (∀ (s : Protocol.PeerState) (channelId : ChannelId) (kind : Protocol.MsgKind),
      Protocol.findChannel s channelId = none → Protocol.resend s channelId kind = none) ∧
  ∀ (c : Protocol.ChannelRecord) (m : Protocol.Msg),
    c.reestablish.nextCommitmentNumber ≤ (c.advanceReceived m).reestablish.nextCommitmentNumber ∧
      c.reestablish.nextRevocationNumber ≤ (c.advanceReceived m).reestablish.nextRevocationNumber ∧
        (c.reestablish.consistent → (c.advanceReceived m).reestablish.consistent)
```

`#print axioms LnLean.Protocol.Peer.reestablish_no_rollback` reports:

```
'LnLean.Protocol.Peer.reestablish_no_rollback' depends on axioms: [propext, Quot.sound]
```

— i.e. only Lean's kernel axioms; no `sorryAx`, no user `axiom`.

The source-level catalog checker (`--allow-planned`, read-only audit) resolves
the target exactly and lists it as a promotion candidate:

```
LN-PR-005 statementOnly theorem no LnLean.Protocol.Peer LnLean.Protocol.Peer.reestablish_no_rollback
Promotion candidates (statementOnly, exact target, theorem/lemma, no sorry)
LN-PR-005: theorem LnLean.Protocol.Peer.reestablish_no_rollback @ LnLean.Protocol.Peer:384
```

The other four rows are still reported as `PLANNED (no declaration yet)`, which
is the intended outcome of this lane: their exact targets do not exist and were
not faked.

`grep` for `sorry|axiom|admit|native_decide|unsafe|implemented_by` in
`LnLean/Protocol/Peer.lean` returns no match.

## 2. LN-PR-005 — **proved exact target**

Catalog claim: *“channel_reestablish retransmits unacknowledged updates without
rolling state back.”*

Added to `LnLean/Protocol/Peer.lean` (line 384), in namespace
`LnLean.Protocol.Peer` so the fully-qualified name is exactly the catalog
target.

### 2.1 Exact statement

```lean
theorem reestablish_no_rollback :
    (∀ (s : PeerState) (channelId : ChannelId) (kind : MsgKind)
        (c : ChannelRecord),
        findChannel s channelId = some c →
          resend s channelId kind = c.lastSent kind) ∧
    (∀ (s : PeerState) (channelId : ChannelId) (kind : MsgKind),
        findChannel s channelId = none → resend s channelId kind = none) ∧
    (∀ (c : ChannelRecord) (m : Msg),
        c.reestablish.nextCommitmentNumber ≤
            (c.advanceReceived m).reestablish.nextCommitmentNumber ∧
        c.reestablish.nextRevocationNumber ≤
            (c.advanceReceived m).reestablish.nextRevocationNumber ∧
        (c.reestablish.consistent → (c.advanceReceived m).reestablish.consistent))
```

Supporting declarations added in `namespace LnLean.Protocol.ChannelRecord`:

```lean
theorem advanceReceived_nextCommitment_ge (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextCommitmentNumber ≤
      (c.advanceReceived m).reestablish.nextCommitmentNumber

theorem advanceReceived_nextRevocation_ge (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextRevocationNumber ≤
      (c.advanceReceived m).reestablish.nextRevocationNumber

theorem advanceReceived_consistent (c : ChannelRecord) (m : Msg)
    (h : c.reestablish.consistent) :
    (c.advanceReceived m).reestablish.consistent
```

### 2.2 Proof approach

* The first conjunct is the existing `resend_of_channel`
  (`simp [resend, h]`), the second the existing `resend_none_of_unknown`.
  These are genuine model facts: `resend` looks up the channel and returns the
  retained `lastSent` field, or `none` when the channel is unknown.
* The counter conjuncts case-split on `m.kind`:
  * `commitmentSigned` ⇒ `afterCommitment` adds one to
    `nextCommitmentNumber` and leaves `nextRevocationNumber` untouched;
  * `revokeAndAck` ⇒ the guard `nextRevocationNumber < nextCommitmentNumber`
    decides whether `afterRevocation` runs; either way neither counter
    decreases;
  * every other kind leaves the record unchanged (`rfl`-level).
  Monotonicity is closed by `omega`.
* Consistency uses the existing `ReestablishFields` lemmas rather than
  reproving arithmetic: `afterCommitment_consistent` for the commitment case
  and `afterRevocation_consistent` (with the guard hypothesis) for the
  revocation case; the unchanged cases are the input hypothesis.

This is not a tautology: the third conjunct is the actual no-rollback
invariant (`next_revocation_number ≤ next_commitment_number` is preserved), and
the monotonicity conjuncts require the case analysis over `advanceReceived`.

### 2.3 What the theorem does and does not claim

* **Does** say: retransmission is exactly the retained last-sent message of the
  requested kind for a known channel; an unknown channel yields nothing; and
  the only reestablish-counter transition in `Peer` is monotone in both
  counters and preserves BOLT 2's consistency condition.
* **Does not** claim: that a peer acknowledged anything (`ChannelRecord` has no
  ack bit; `lastSent kind` *is* the unacknowledged copy), that an update was
  ever sent, that older unacknowledged updates are retained (the model keeps
  only the last message per kind, so `recordSent` overwrites), or that a
  `channel_reestablish` wire message is built or scheduled. `resend` is an
  explicit operation, not an automatic retransmission policy.

### 2.4 Promotion

**Promotion-ready: yes.** The exact catalog target exists, is kernel-checked,
depends only on `propext`/`Quot.sound`, and the audit checker lists it as a
promotion candidate. The catalog row is still `status := .statementOnly` in
`LnLean/Proofs/Obligations.lean`; this lane is forbidden to edit that file, so
the integrator must flip that one row to `.proved`. `Traceability.lean` already
maps the name to module `LnLean.Protocol.Peer`, so no traceability retarget is
needed.

## 3. LN-PR-001 — `Handshake.open_bounds` (blocked at target)

Catalog claim: *“open_channel accepts a funding amount only above the dust and
minimum-channel bounds.”*

**Model gap.** `LnLean/Protocol/Handshake.lean` has no `open_channel` fields at
all: `open_channel` is deliberately not a `Msg` constructor
(`Messages.lean` “What is NOT modelled”), and `HandshakeEvent.sendAcceptChannel`
carries no payload. There is therefore no funding amount to bound and no
`open_bounds` declaration to prove in that module. Adding one would require
introducing a second `open_channel` record into `Handshake`, duplicating the
faithful model that already exists and changing the wave-A interface; that
would not be the catalog claim.

**Faithful existing model.** `LnLean/Proofs/WaveD/D17.lean` defines

```lean
structure OpenChannelMsg where
  fundingSatoshis : Nat
  pushMsat : Msat
  dustLimitSatoshis : Nat
  channelReserveSatoshis : Nat

structure AcceptPolicy where
  minFundingSatoshis : Nat
  supportsLargeChannel : Bool := false

def OpenChannelMsg.accepts (p : AcceptPolicy) (m : OpenChannelMsg) : Prop := …
def acceptOpenChannel (p : AcceptPolicy) (m : OpenChannelMsg) :
    Option OpenChannelAcceptance
```

and proves at `D17.lean:204`:

```lean
theorem waveD_d17_open_bounds {p : AcceptPolicy} {m : OpenChannelMsg}
    {a : OpenChannelAcceptance}
    (h : acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis < m.fundingSatoshis ∧
    minChannelValueSatoshis ≤ m.fundingSatoshis ∧
    p.minFundingSatoshis ≤ m.fundingSatoshis
```

plus rejection directions (`waveD_d17_reject_of_funding_le_dust`, etc.). This
is the faithful acceptor model the brief refers to. `D17` imports
`Handshake`, so an alias theorem named `Handshake.open_bounds` cannot be
defined in `Handshake` without an import cycle.

**Fresh theorem added: none.** A conditional restatement in `Handshake` would
either be unmoored (no fields) or a duplicate of D17 at the wrong layer.

**Promotion verdict: no** at `LnLean.Protocol.Handshake.open_bounds`. The claim
is true in D17's model, so the correct repair is a catalog retarget (and a
brief note that the wave-A `Handshake` module does not model `open_channel`),
not a new proof at the stale name.

## 4. LN-PR-003 — `Handshake.funding_signed_valid` (blocked at target)

Catalog claim: *“funding_signed carries a valid signature over the funding
transaction.”*

**Model gap.** In `LnLean/Protocol/Messages.lean`,
`FundingSigned` is only

```lean
structure FundingSigned where
  channelId : ChannelId
  signature : EcdsaSig
```

and `wellFormed` checks `idsValid`, `sigsValid` and `semanticOk`; for
signatures `sigsValid` only proves `s.bytes.size ≤ 73`
(`wellFormed_signature`). There is no funding transaction, no key, and no
verification call. Claiming “valid signature” from `wellFormed` would be
exactly the length-check fallacy the brief forbids, and it is also false:
E19 proves an unconditional-form counterexample.

**Faithful existing model.** `LnLean/Proofs/WaveE/E19.lean` defines
(`E19.lean:83`)

```lean
def fundingSignedValid (M : PrimitiveModel) (fundingKey : PubKey)
    (fundingTx : ByteArray) (m : FundingSigned) : Prop :=
  verifyFundingChecked M fundingKey fundingTx m.signature = true
```

and proves (`E19.lean:92`) the exact characterization

```lean
theorem waveE_e19_funding_signed_valid_iff (M : PrimitiveModel)
    (fundingKey : PubKey) (fundingTx : ByteArray) (m : FundingSigned) :
    fundingSignedValid M fundingKey fundingTx m ↔
      wireSigOK m.signature.bytes = true ∧
        fundingSignedVerifies M fundingKey fundingTx m
```

together with message binding under `EufCma` and sig-shape consequences.
`E19.lean:294` proves the unconditional reading is false:

```lean
theorem waveE_e19_unconditional_form_false (M₀ : PrimitiveModel) :
    ∃ m : FundingSigned,
      wellFormed (.fundingSigned m) ∧ ¬ fundingSignedAlwaysValid m
```

`E19` also records that `HandshakeEvent.sendFundingSigned` carries no message,
so no reachable handshake event can establish signature validity.

**Fresh theorem added: none.** The most one could state in `Handshake` is the
length bound (`wellFormed_signature` already exists), which is the gap, not the
claim; naming that `funding_signed_valid` would be fake.

**Promotion verdict: no** at the exact target. Retarget to
`LnLean.Proofs.WaveE.E19.fundingSignedValid` +
`waveE_e19_funding_signed_valid_iff` / `_sound`, with the claim reworded to
“given the verifier model, funding key and funding-transaction bytes, a
`funding_signed` valid predicate means …”.

## 5. LN-PR-004 — `Messages.commitment_signed_covers` (blocked at target)

Catalog claim: *“commitment_signed covers exactly the current HTLC set and
fee.”*

**Model gap.** `Messages.CommitmentSigned` is

```lean
structure CommitmentSigned where
  channelId : ChannelId
  signature : EcdsaSig
  htlcSignatures : List EcdsaSig
```

with no commitment transaction, no HTLC set, no fee or feerate, and no
commitment number. `wellFormed` only bounds signature lengths. There is no
declaration `commitment_signed_covers` in `Messages.lean` and no data from
which to define it.

**Faithful existing model.** `LnLean/Proofs/WaveE/E20.lean` defines
(`E20.lean:180`)

```lean
def waveE_e20_commitment_signed_covers (m : CommitmentSigned) (r : FeeRate)
    (c : Commitment) : Prop :=
  waveE_e20_covers_htlcs m c ∧ waveE_e20_covers_fee r c
```

where `waveE_e20_covers_htlcs` is `m.htlcSignatures.length = c.htlcs.length`
(the positional “one per untrimmed HTLC output”) and `waveE_e20_covers_fee` is
the BOLT 3 fee equation, and proves the bundled statement
`waveE_e20_commitment_signed_covers_exact` (`E20.lean:247`).

The unconditional reading is **false** in the wave-A model, as E20 proves:

* `waveE_e20_commitment_signed_covers_unconditional_false` (`E20.lean:314`);
* `waveE_e20_same_message_different_htlc_sets` — one message can “cover” two
  commitments with different HTLC sets of the same cardinality;
* `waveE_e20_wellFormed_empty_signatures` — the decoder accepts an empty
  signature list.

Coverage is a predicate relating the wire message to an externally supplied
`Commitment`; it is not derivable from the message alone. The missing links are
the signed-commitment relation and cryptographic verification (assumption C3).

**Fresh theorem added: none.** Restating E20 in `Messages` would require
importing `LnLean.Channel.Commitment` into the wire module (a layering change)
or introducing a second, weaker “covers” predicate, which would not be the
claim.

**Promotion verdict: no** at the exact target. Retarget to
`LnLean.Proofs.WaveE.E20.waveE_e20_commitment_signed_covers` (+
`waveE_e20_commitment_signed_covers_exact`), and reword the claim to be
relative to a commitment transaction.

## 6. LN-PR-006 — `Handshake.feature_intersection` (blocked at target)

Catalog claim: *“Negotiated channel features are the intersection of both
peers' supported features.”*

**Model gap.** `Messages.InitMsg` carries

```lean
structure InitMsg where
  globalfeatures : ByteArray := ByteArray.empty
  features : ByteArray := ByteArray.empty
```

and `HandshakeState` records only whether `init` was sent/received; feature
bytes are opaque and never inspected. There is no `feature_intersection`
declaration, no bit predicate, and no notion of support in
`Handshake.lean`. A theorem there could only be a statement about opaque byte
arrays, which is not the claim.

**Faithful existing model (with a wording caveat).** The feature-vector model
lives in `LnLean/Proofs/Protocol/FeaturesProps.lean` and
`LnLean/Proofs/PhaseC2/FeatureClosure.lean`. Its relevant facts are:

* `feature_intersection` analogue: `intersection f g` is the pointwise AND;
  `intersection_required_iff` (`FeatureClosure.lean:145`) proves the even
  (required) bit of feature `n` is set iff it is set in both operands.
* Acceptance is closed under intersection:
  `accepts_intersection` (`FeatureClosure.lean:121`).
* Support sets shrink: `supportSet_intersection_subset`
  (`FeatureClosure.lean:355`) states every feature supported by the
  intersection is supported by both operands.
* But the reverse inclusion fails, and raw bitwise intersection is **not** BOLT
  1 negotiation: `FeaturesProps.bitwiseIntersection_not_negotiation`
  (`FeaturesProps.lean:400`) gives two peers that both support feature 0
  (one optional, one required) whose bitwise AND supports neither bit.
  Negotiated support is `mutualSupport`, not raw `intersection`
  (`FeaturesProps.lean:276`, `:287`).

So even the faithful feature-vector model does not support the catalog sentence
literally. The true statement is about **required bits** (and acceptance), not
about “supported features” under raw intersection.

**Fresh theorem added: none.**

**Promotion verdict: no** at the exact target, and the claim itself needs
rewording. Recommended retarget: `intersection_required_iff` +
`accepts_intersection` + `supportSet_intersection_subset`, with the claim
phrased as “the required-bit part of the negotiated intersection is the
conjunction of the peers' required bits; raw bitwise intersection is not
negotiation in general.”

## 7. Files changed

| File | Change |
|---|---|
| `LnLean/Protocol/Peer.lean` | +107 lines: section “Reestablish: retransmission without rollback”, three `ChannelRecord` lemmas, and the exact target `LnLean.Protocol.Peer.reestablish_no_rollback`. Existing declarations/comments untouched. |
| `agents/reports/P01-PROTOCOL.md` | this report (new) |

No changes to `Handshake.lean` (no faithful exact statement was available for
the four blocked rows), no changes to `Obligations.lean`, `Traceability.lean`,
`scripts/`, `vendor/`, or any other lane's files. No git add/commit/push or
branch change was performed.

## 8. Residual risks and recommendations

1. **LN-PR-005 status flip is integrator work.** The theorem is done, but
   `Obligations.lean:258` still says `.statementOnly`; this lane is barred from
   editing the catalog. Until that line flips, strict catalog runs will keep
   treating the row as statement-only even though the target resolves.
2. **Four rows need retargeting, not proofs at the stale names.** The claims
   are either modelled in a different module (D17/E19/E20/FeatureClosure) or,
   for LN-PR-004 and LN-PR-006, false/imprecise in the wave-A model until
   qualified. Adding declarations named `open_bounds`, `funding_signed_valid`,
   `commitment_signed_covers`, or `feature_intersection` in `Handshake` /
   `Messages` without their model fields would be dishonest and would not
   survive review.
3. **Reference names in §3–§6 were checked by source inspection, not rebuilt in
   this lane.** Their modules currently have unrelated unbuilt dependencies in
   this workspace (e.g. `LnLean.Channel.Commitment` has a source edit from
   another lane and no `.olean`), so rebuilding them would compile another
   lane's in-progress file. The line numbers and statements above are the
   committed source text; the only module this lane rebuilt and `#check`ed is
   `LnLean.Protocol.Peer`.
4. **LN-PR-005 is a model-level theorem.** Promotion should be accompanied by
   the caveats in §2.3 (no ack bit, only the last message per kind is retained,
   no automatic retransmission or message construction) so the catalog claim is
   not read as a full BOLT 2 retransmission scheduler.
