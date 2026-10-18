# PR-WRAPPERS — faithful wrappers for LN-PR-001/003/004/006

Lane: `PR-WRAPPERS`, branch `repair/integrated`, base HEAD `0caec3d`.
Scope: protocol rows `LN-PR-001`, `LN-PR-003`, `LN-PR-004`, `LN-PR-006`.

## 1. Files changed

| File | Change |
|---|---|
| `LnLean/Proofs/ProtocolTargets.lean` | New module. Imports `WaveD.D17`, `WaveE.E19`, `WaveE.E20`, `WaveE.E22`; defines the four faithful catalog wrappers that have exact statements. |
| `agents/reports/PR-WRAPPERS.md` | This report. |

No existing declaration or comment was modified. No edits to `Obligations.lean`,
`Traceability.lean`, scripts, vendor, docs, root imports, or another lane's
files. No commit, push, or revert was performed.

## 2. Wrappers and exact signatures

All wrappers live in `LnLean/Proofs/ProtocolTargets.lean`.

### LN-PR-001 — `LnLean.Protocol.Handshake.open_bounds`

Restates `LnLean.Proofs.WaveD.D17.waveD_d17_open_bounds` exactly. The
hypothesis is the D17 acceptor transition `acceptOpenChannel p m = some a`; it
does not assume any of the three bounds.

```lean
theorem LnLean.Protocol.Handshake.open_bounds
    {p : LnLean.Proofs.WaveD.D17.AcceptPolicy}
    {m : LnLean.Proofs.WaveD.D17.OpenChannelMsg}
    {a : LnLean.Proofs.WaveD.D17.OpenChannelAcceptance}
    (h : LnLean.Proofs.WaveD.D17.acceptOpenChannel p m = some a) :
    m.dustLimitSatoshis < m.fundingSatoshis ∧
      LnLean.Proofs.WaveD.D17.minChannelValueSatoshis ≤ m.fundingSatoshis ∧
      p.minFundingSatoshis ≤ m.fundingSatoshis
```

### LN-PR-003 — `LnLean.Protocol.Handshake.funding_signed_valid`

Restates `LnLean.Proofs.WaveE.E19.waveE_e19_funding_signed_valid_iff`: the
checked validity predicate is exactly BOLT wire-shape acceptance plus
funding-domain ECDSA verification under an explicitly supplied verifier
model, funding key, and funding-transaction bytes. The funding key and
transaction are parameters because the wave-A `FundingSigned` record has no
fields for them. This is not a length-only claim and does not assume validity
as a hypothesis.

```lean
theorem LnLean.Protocol.Handshake.funding_signed_valid
    (M : LnLean.Crypto.PrimitiveModel) (fundingKey : LnLean.PubKey)
    (fundingTx : ByteArray) (m : LnLean.Protocol.FundingSigned) :
    LnLean.Proofs.WaveE.E19.fundingSignedValid M fundingKey fundingTx m ↔
      LnLean.Crypto.wireSigOK m.signature.bytes = true ∧
        LnLean.Proofs.WaveE.E19.fundingSignedVerifies M fundingKey fundingTx m
```

### LN-PR-004 — `LnLean.Protocol.Messages.commitment_signed_covers`

Restates the bundled conditional theorem
`LnLean.Proofs.WaveE.E20.waveE_e20_commitment_signed_covers_exact`. The
coverage predicate is an explicit hypothesis relating the wire message to a
supplied `Commitment` and `FeeRate`; the wrapper does not state the false
unconditional reading. The signature-count and payload-bound conjuncts are
not part of the coverage hypothesis.

```lean
theorem LnLean.Protocol.Messages.commitment_signed_covers
    (m : LnLean.Protocol.CommitmentSigned) (r : LnLean.FeeRate)
    (c : LnLean.Channel.Commitment)
    (hc : LnLean.Proofs.WaveE.E20.waveE_e20_commitment_signed_covers m r c)
    (hwf : LnLean.Protocol.wellFormed (LnLean.Protocol.Msg.commitmentSigned m)) :
    m.htlcSignatures.length = c.htlcs.length ∧
      (LnLean.Protocol.signatures (LnLean.Protocol.Msg.commitmentSigned m)).length =
        c.htlcs.length + 1 ∧
      LnLean.Protocol.msgLength (LnLean.Protocol.Msg.commitmentSigned m) ≤
        34 + 73 + 73 * c.htlcs.length ∧
      c.feeSat = (LnLean.Channel.commitmentFee r c).val
```

### LN-PR-006 — `LnLean.Protocol.Handshake.feature_intersection`

Restates `LnLean.Proofs.WaveE.E22.waveE_e22_negotiated_eq_featureIntersection`.
The catalog sentence is read as the intersection of the two *support sets*
(`featureIntersection`, definitionally `FeaturesProps.mutualSupport`), not as
a bitwise AND of the raw feature vectors. The `hAccept` hypothesis is BOLT 1's
survival condition: the peer supports every feature the local node requires.
It is not an assumption of the conclusion; it is the condition under which
the asymmetric `negotiated` rule collapses to the symmetric intersection.

```lean
theorem LnLean.Protocol.Handshake.feature_intersection
    (lcl rmt : LnLean.Proofs.Protocol.FeatureVector)
    (hAccept : ∀ n, lcl.requires n = true → rmt.supports n = true)
    (n : Nat) :
    LnLean.Proofs.Protocol.negotiated lcl rmt n =
      LnLean.Proofs.WaveE.E22.featureIntersection lcl rmt n
```

The raw bitwise reading remains false
(`LnLean.Proofs.Protocol.bitwiseIntersection_not_negotiation`,
`waveE_e22_bitwise_and_not_support_intersection`), and the unconditional
reading is false (`waveE_e22_unconditional_claim_false`); see §5.

## 3. Name and axiom checks

Command (one Lean process, under the repository build lock):

```sh
lake env lean /tmp/opencode/pr_wrappers_check.lean
```

The check file imports `LnLean.Proofs.ProtocolTargets` and runs `#check` plus
`#print axioms`. Exit code: `0`.

```text
'LnLean.Protocol.Handshake.open_bounds' depends on axioms: [propext]
'LnLean.Protocol.Handshake.funding_signed_valid'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'LnLean.Protocol.Messages.commitment_signed_covers'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'LnLean.Protocol.Handshake.feature_intersection' depends on axioms: [propext]
```

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, or
`@[implemented_by]` occurs in the new module. The standard classical axioms in
the funding and commitment wrappers come from the pre-existing D/E proof
dependencies, not from new assumptions.

## 4. Build and import-cycle checks

Direct elaboration of the new module:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Proofs/ProtocolTargets.lean
# RC=0
```

Lake target build:

```sh
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.ProtocolTargets
# ✔ [25/25] Built LnLean.Proofs.ProtocolTargets (635ms)
# Build completed successfully (25 jobs).
# RC=0
```

Import direction is acyclic:

* `ProtocolTargets` imports `D17`, `E19`, `E20`, `E22`;
* `D17`/`E19`/`E20`/`E22` import wave-A protocol modules, `Crypto`,
  `Channel.Commitment`, and `FeaturesProps`, never `ProtocolTargets`;
* `grep -rn "import LnLean.Proofs.ProtocolTargets" LnLean` returns no match.

`git status --short` shows `?? LnLean/Proofs/ProtocolTargets.lean` plus this
report. The other modified/untracked paths in the worktree belong to other
lanes and were not touched.

## 5. Per-row promotion verdict

### LN-PR-001 — promotion-ready after root import and provenance note

The wrapper is proved, is not a tautology, and depends only on `propext`. The
catalog name now resolves **provided the parent imports
`LnLean.Proofs.ProtocolTargets`** and retargets the traceability entry from
`LnLean.Protocol.Handshake` to `LnLean.Proofs.ProtocolTargets` (the
`Obligations.lean` target string can stay the same once the module is
imported).

Caveat: the statement is about D17's `OpenChannelMsg` / `AcceptPolicy` /
`acceptOpenChannel`, not about a field of wave-A `HandshakeState`. The wave-A
`Handshake` module still does not model `open_channel`; the catalog/claim
should record that the bound is proved in the faithful acceptor model.

### LN-PR-003 — conditional promotion only; literal claim remains false

The wrapper is proved at the catalog name, with the standard classical axiom
set. It is faithful only as a **conditional** statement parameterized by the
primitive model, funding key, and funding-transaction bytes. The literal
unconditional claim ("every `FundingSigned` carries a valid signature") is
false in the wave-A model; E19's counterexample still applies. Promote only
if the catalog claim is reworded to the conditional form and the traceability
entry points at `LnLean.Proofs.ProtocolTargets` (or directly at
`LnLean.Proofs.WaveE.E19`). Otherwise keep the row blocked/statement-only.

### LN-PR-004 — conditional promotion only; literal claim remains false

The wrapper is proved at the catalog name, with the standard classical axiom
set. Coverage is relative to a supplied commitment transaction and feerate,
and the theorem is conditional on the coverage predicate plus wire
well-formedness. The unconditional reading is false (E20's
`waveE_e20_commitment_signed_covers_unconditional_false`, the empty-signature
example, and the same-message/different-HTLC-sets example). Promote only with
the claim reworded to "given a commitment transaction and coverage predicate,
..." and the traceability entry retargeted to
`LnLean.Proofs.ProtocolTargets` (or `LnLean.Proofs.WaveE.E20`).

### LN-PR-006 — conditional promotion after rewording; raw bitwise reading is false

The wrapper is proved at the catalog name and depends only on `propext`. It is
faithful only when "intersection of both peers' supported features" is read as
the intersection of the two **support sets** (`featureIntersection`, which is
`mutualSupport`), not as a bitwise AND of the raw feature vectors, and only
under BOLT 1's survival hypothesis `hAccept`.

The raw bitwise claim is false:
`LnLean.Proofs.Protocol.bitwiseIntersection_not_negotiation` and
`LnLean.Proofs.WaveE.E22.waveE_e22_bitwise_and_not_support_intersection`
exhibit two peers that both support feature 0 (one through the odd bit, one
through the even bit) whose bitwise AND supports neither bit. The
unconditional negotiation claim is also false:
`waveE_e22_unconditional_claim_false` has a required-only local vector whose
negotiated set is non-empty against an empty peer vector. The full BOLT 1
`negotiated` rule is not unconditionally commutative
(`negotiated_not_commutative`).

Promotion therefore requires a claim rewording such as: "On a surviving BOLT 1
connection (the peer supports every locally required feature), negotiated
channel features are the intersection of the two peers' supported-feature
sets; this is support-set intersection, not a bitwise AND of the feature
vectors." The traceability entry should point at
`LnLean.Proofs.ProtocolTargets` (or `LnLean.Proofs.WaveE.E22`). Additional
faithful facts available for the same row:

* `LnLean.Proofs.PhaseC2.intersection_required_iff` — a required bit survives
  bitwise intersection iff both peers require it;
* `LnLean.Proofs.PhaseC2.accepts_intersection` — acceptance is closed under
  bitwise intersection;
* `LnLean.Proofs.PhaseC2.supportSet_intersection_subset` — the support set of
  the intersection is contained in both peers' support sets (the reverse
  inclusion fails);
* `LnLean.Proofs.WaveE.E22.waveE_e22_negotiatedSet_eq_inter` — set-level form
  of the same conditional equality;
* `LnLean.Proofs.Protocol.mutualSupport` /
  `negotiated_eq_mutualSupport_of_peer_supports` — the underlying
  `FeaturesProps` formulation.

## 6. Residual notes for the parent

1. The four wrappers are additive and live outside the wave-A modules, so no
   model-layer interface changed.
2. `Obligations.lean` still marks all four rows `.statementOnly`; only the
   parent may flip statuses.
3. `Traceability.lean` currently maps the four wrapped names to
   `LnLean.Protocol.Handshake` / `LnLean.Protocol.Messages`; those module
   fields are stale for the faithful models and should point at
   `LnLean.Proofs.ProtocolTargets` (or the D/E source modules).
4. If the parent adds `import LnLean.Proofs.ProtocolTargets` to a root
   aggregator, the four catalog names resolve without touching
   `Obligations.lean`'s target strings.
