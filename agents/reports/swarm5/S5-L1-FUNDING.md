# S5-L1-FUNDING — funding witness-script hash link constructed from handshake data

**Lane:** `S5-L1-FUNDING` (`L1-03`, `L1-05`).
**Verdict:** complete for the assigned scope. `FundingScriptHashLinked` is no
longer an assumption on the modelled handshake path: `FundingNegotiation`
carries no hash field, and `toFundingParams H` *computes* the P2WSH program as
`H (witnessScript.bytes)`, so the link is `rfl`. The reverse direction keeps
the finite pair-level `CollisionFreeOn` admission; no global SHA-256
injectivity and no 32-byte C1 claim is used. A mechanised counterexample shows
that `accept_channel` alone does not determine the witness script, because the
opener's `open_channel` key is not a field of the modelled message.

- Repository: `/home/ubuntu/ln-lean-repair`
- Branch: `repair/integrated`
- Base commit: `79a92ce`
- Lane files:
  - `LnLean/Bitcoin/Funding.lean` (modified, additive)
  - `LnLean/Protocol/Handshake.lean` (modified, additive)
  - `LnLean/Proofs/Bitcoin/FundingLinkTargets.lean` (new, 564 lines)
  - `agents/reports/swarm5/S5-L1-FUNDING.md` (this report)
- No existing model/proof file outside the lane set, `LnLean.lean`, catalog,
  traceability, audit, shared doc/script, vendor tree, or Git history was
  touched. No Git write was performed. The other uncommitted changes in the
  worktree belong to other lanes and were left alone.

## 1. What was wrong, and what changed

`LnLean.Proofs.Bitcoin.FundingScriptTargets` proved the `LN-L1-001` output
shape only under

```lean
FundingScriptHashLinked H p := p.witnessScriptHash = H p.witnessScript.bytes
```

because `FundingParams.witnessScriptHash` is a free record field. The
hypothesis is satisfiable, but nothing in the model prevented a caller from
pairing the correct keys with an unrelated 32-byte program, and nothing tied
the handshake messages to that field.

This lane adds the missing construction layer:

1. **`FundingScript`** (`LnLean/Bitcoin/Funding.lean`, new structure) carries
   the local/remote key orientation, the lexicographically ordered pair
   actually serialized, and the BOLT 3 script bytes.
   `FundingScript.ofKeys a b` builds `OP_2 <pk1> <pk2> OP_2 OP_CHECKMULTISIG`
   with `pk1/pk2 = orderedFundingKeys a b`.
2. **`FundingNegotiation`** (new structure) carries `fundingSatoshis`,
   `pushMsat`, `localFundingKey`, `remoteFundingKey`,
   `temporaryChannelId`, and `finalChannelId?`. It deliberately has **no**
   `witnessScriptHash` field.
3. **`FundingNegotiation.toFundingParams H`** computes
   `witnessScriptHash := H n.witnessScript.bytes`. The link is therefore
   definitional; there is no argument through which a caller can inject an
   unrelated program.
4. **`AcceptChannel.toFundingNegotiation` / `.toFundingParams`** in
   `LnLean/Protocol/Handshake.lean` read the peer's key from
   `accept_channel.funding_pubkey`; the opener's fields remain explicit local
   values because this model has no `open_channel` constructor.
5. **`FundingLinkTargets`** lifts the construction to the existing targets:
   ordered P2WSH output, the old disjunctive `TwoOfTwo` form with its hash
   hypothesis discharged, confirmed-output byte shape, the SHA-256 instance,
   finite reverse binding, non-vacuity, and the non-determination
   counterexample.

The important design choice is the abstract hash parameter
`H : ByteArray → ByteArray`. The forward construction is correct for any `H`;
specialising `H := M.sha256` gives the `PrimitiveModel` form. This avoids
assuming that the model's opaque `M.sha256` is the FIPS 180-4 function, which
the Lean development does not prove.

## 2. Exact signatures

All statements below were checked with `#check @...` against the built
environment. Names are fully qualified; `H : ByteArray → ByteArray`,
`n m : FundingNegotiation`, and `p : FundingParams`.

### 2.1 Construction (`LnLean.Bitcoin`)

```lean
structure FundingScript where
  localFundingKey : PubKey
  remoteFundingKey : PubKey
  firstFundingKey : PubKey
  secondFundingKey : PubKey
  witnessScript : Script

FundingScript.ofKeys : PubKey → PubKey → FundingScript

theorem FundingScript.ofKeys_witnessScript_bytes (a b : PubKey) :
    (FundingScript.ofKeys a b).witnessScript.bytes =
      (ByteArray.empty.push 0x52)
        ++ pushData (orderedFundingKeys a b).1.bytes
        ++ pushData (orderedFundingKeys a b).2.bytes
        ++ (ByteArray.empty.push 0x52)
        ++ (ByteArray.empty.push OP_CHECKMULTISIG)

theorem FundingScript.ofKeys_witnessScript_eq_witnessScript (p : FundingParams) :
    (FundingScript.ofKeys p.localFundingKey p.remoteFundingKey).witnessScript =
      p.witnessScript

theorem FundingScript.ofKeys_witnessScript_eq_ordered_pair (a b : PubKey) :
    (FundingScript.ofKeys a b).witnessScript.bytes =
      (ByteArray.empty.push 0x52)
        ++ pushData (FundingScript.ofKeys a b).firstFundingKey.bytes
        ++ pushData (FundingScript.ofKeys a b).secondFundingKey.bytes
        ++ (ByteArray.empty.push 0x52)
        ++ (ByteArray.empty.push OP_CHECKMULTISIG)

structure FundingNegotiation where
  fundingSatoshis : BtcAmount
  pushMsat : Msat
  localFundingKey : PubKey
  remoteFundingKey : PubKey
  temporaryChannelId : TemporaryChannelId
  finalChannelId? : Option FinalChannelId := none

FundingNegotiation.witnessScript : FundingNegotiation → Script
FundingNegotiation.firstFundingKey : FundingNegotiation → PubKey
FundingNegotiation.secondFundingKey : FundingNegotiation → PubKey

FundingNegotiation.toFundingParams :
    (ByteArray → ByteArray) → FundingNegotiation → FundingParams

theorem FundingNegotiation.toFundingParams_witnessScriptHash
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (FundingNegotiation.toFundingParams H n).witnessScriptHash =
      H (FundingNegotiation.toFundingParams H n).witnessScript.bytes

theorem FundingNegotiation.toFundingParams_fundingScriptPubKey
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (FundingNegotiation.toFundingParams H n).fundingScriptPubKey =
      p2wsh (H (FundingNegotiation.toFundingParams H n).witnessScript.bytes)

theorem FundingNegotiation.toFundingParams_witnessScriptHash_size
    (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (n : FundingNegotiation) :
    (FundingNegotiation.toFundingParams H n).witnessScriptHash.size = 32

theorem FundingNegotiation.toFundingParams_wellFormed
    (H : ByteArray → ByteArray)
    (hH : ∀ b : ByteArray, (H b).size = 32) (n : FundingNegotiation)
    (hsat0 : 0 ≤ n.fundingSatoshis)
    (hsatMax : n.fundingSatoshis ≤ Bitcoin.Data.MAX_MONEY)
    (hlocal : n.localFundingKey.Valid)
    (hremote : n.remoteFundingKey.Valid)
    (hpush : ↑n.pushMsat.val ≤
      n.fundingSatoshis * ↑Msat.MSAT_PER_SAT) :
    (FundingNegotiation.toFundingParams H n).WellFormed
```

The `@[simp]` projections `toFundingParams_fundingSatoshis`,
`toFundingParams_pushMsat`, `toFundingParams_localFundingKey`,
`toFundingParams_remoteFundingKey`, `toFundingParams_temporaryChannelId`,
`toFundingParams_finalChannelId`, and `toFundingParams_witnessScript` are also
present and `rfl`.

### 2.2 Handshake bridge (`LnLean.Protocol`)

```lean
AcceptChannel.toFundingNegotiation :
    PubKey → BtcAmount → Msat → TemporaryChannelId → AcceptChannel →
      FundingNegotiation

AcceptChannel.toFundingParams :
    (ByteArray → ByteArray) → PubKey → BtcAmount → Msat →
      TemporaryChannelId → AcceptChannel → FundingParams

theorem AcceptChannel.toFundingNegotiation_remoteFundingKey
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount)
    (pushMsat : Msat) (temporaryChannelId : TemporaryChannelId)
    (m : AcceptChannel) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).remoteFundingKey = m.fundingPubKey

theorem AcceptChannel.toFundingNegotiation_localFundingKey
    (localFundingKey : PubKey) (fundingSatoshis : BtcAmount)
    (pushMsat : Msat) (temporaryChannelId : TemporaryChannelId)
    (m : AcceptChannel) :
    (m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId).localFundingKey = localFundingKey

theorem AcceptChannel.toFundingParams_witnessScriptHash
    (H : ByteArray → ByteArray) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) (m : AcceptChannel) :
    (AcceptChannel.toFundingParams H localFundingKey fundingSatoshis pushMsat
        temporaryChannelId m).witnessScriptHash =
      H ((AcceptChannel.toFundingParams H localFundingKey fundingSatoshis
        pushMsat temporaryChannelId m).witnessScript.bytes)

theorem acceptReceived_of_sendFundingCreated {s s' : HandshakeState}
    (h : handshakeStep s HandshakeEvent.sendFundingCreated = some s') :
    s.acceptReceived = true

theorem acceptReceived_of_recvAcceptChannel {s s' : HandshakeState}
    (h : handshakeStep s HandshakeEvent.recvAcceptChannel = some s') :
    s'.acceptReceived = true
```

`acceptReceived_of_sendFundingCreated` is the ordering guarantee: the peer's
`funding_pubkey` is available before the funding output may be built, because
`funding_created` is guarded by `canSendFundingCreated`, which requires
`acceptReceived`.

### 2.3 Targets (`LnLean.Proofs.Bitcoin.FundingLinkTargets`)

```lean
theorem toFundingParams_hash_linked (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    FundingScriptHashLinked H (n.toFundingParams H)

theorem toFundingParams_hash_linked_sha256 (M : PrimitiveModel)
    (n : FundingNegotiation) :
    FundingScriptHashLinked M.sha256 (n.toFundingParams M.sha256)

theorem toFundingParams_witnessScriptHash_size_sha256 (M : PrimitiveModel)
    (n : FundingNegotiation) :
    (n.toFundingParams M.sha256).witnessScriptHash.size = 32

theorem toFundingParams_scriptPubKey_eq_p2wsh (H : ByteArray → ByteArray)
    (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
      p2wsh (H (n.toFundingParams H).witnessScript.bytes)

theorem witnessScript_bytes_eq_TwoOfTwoScriptBytes (n : FundingNegotiation) :
    n.witnessScript.bytes =
      TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey

theorem ofKeys_witnessScript_isTwoOfTwo (a b : PubKey) :
    IsTwoOfTwoScript a b (FundingScript.ofKeys a b).witnessScript.bytes

theorem toFundingParams_witnessScript_bytes_eq_TwoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScript.bytes =
      TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey

theorem fundingScriptPubKey_eq_p2wsh_ordered
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
      p2wsh (H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey))

theorem fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (n.toFundingParams H).localFundingKey
          (n.toFundingParams H).remoteFundingKey)) ∨
      (n.toFundingParams H).fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes
          (n.toFundingParams H).remoteFundingKey
          (n.toFundingParams H).localFundingKey))

theorem witnessScriptHash_eq_hash_TwoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation) :
    (n.toFundingParams H).witnessScriptHash =
      H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey)
```

Handshake-level forms:

```lean
theorem acceptChannel_funding_link (H : ByteArray → ByteArray)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let p := m.toFundingParams H localFundingKey fundingSatoshis pushMsat
      temporaryChannelId
    p.localFundingKey = localFundingKey ∧
      p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash = H p.witnessScript.bytes ∧
      (p.fundingScriptPubKey =
          p2wsh (H (TwoOfTwoScriptBytes p.localFundingKey
            p.remoteFundingKey)) ∨
        p.fundingScriptPubKey =
          p2wsh (H (TwoOfTwoScriptBytes p.remoteFundingKey
            p.localFundingKey)))

theorem acceptChannel_funding_link_sha256 (M : PrimitiveModel)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let p := m.toFundingParams M.sha256 localFundingKey fundingSatoshis
      pushMsat temporaryChannelId
    p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash = M.sha256 p.witnessScript.bytes ∧
      p.witnessScriptHash.size = 32

theorem acceptChannel_funding_link_ordered (H : ByteArray → ByteArray)
    (m : AcceptChannel) (localFundingKey : PubKey)
    (fundingSatoshis : BtcAmount) (pushMsat : Msat)
    (temporaryChannelId : TemporaryChannelId) :
    let n := m.toFundingNegotiation localFundingKey fundingSatoshis pushMsat
      temporaryChannelId
    let p := n.toFundingParams H
    p.remoteFundingKey = m.fundingPubKey ∧
      p.witnessScriptHash =
        H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey) ∧
      p.fundingScriptPubKey =
        p2wsh (H (TwoOfTwoScriptBytes n.firstFundingKey
          n.secondFundingKey))
```

`acceptChannel_funding_link_ordered` is the strongest handshake statement: it
has no disjunction and identifies the exact ordered BOLT 3 bytes.

Output-level forms:

```lean
theorem toFundingOutput_scriptPubKey_eq_p2wsh
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    (txid : ByteArray) (index : Nat) :
    ((n.toFundingParams H).toFundingOutput txid index).scriptPubKey =
      p2wsh (H (n.toFundingParams H).witnessScript.bytes)

theorem fundingConfirmed_script_commits_constructed
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    {tx : Tx} {index : Nat}
    (hc : FundingConfirmed (n.toFundingParams H) tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 32 ++
          H (n.toFundingParams H).witnessScript.bytes

theorem fundingConfirmed_script_commits_TwoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    {tx : Tx} {index : Nat}
    (hc : FundingConfirmed (n.toFundingParams H) tx index) :
    ∃ out : TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        (ByteArray.empty.push OP_0).push 32 ++
          H (TwoOfTwoScriptBytes n.firstFundingKey n.secondFundingKey)
```

Reverse binding and non-vacuity:

```lean
theorem constructed_binds_twoOfTwo
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    (hwf : (n.toFundingParams H).WellFormed) (revealed : ByteArray)
    (hrev : (n.toFundingParams H).fundingScriptPubKey = p2wsh (H revealed))
    (hc1 : CollisionFreeOn H revealed
      (n.toFundingParams H).witnessScript.bytes) :
    IsTwoOfTwoScript (n.toFundingParams H).localFundingKey
        (n.toFundingParams H).remoteFundingKey revealed ∧
      revealed.size = 71

theorem constructed_binds_witnessScript
    (H : ByteArray → ByteArray) (n : FundingNegotiation)
    (revealed : ByteArray)
    (hrev : (n.toFundingParams H).witnessScriptHash = H revealed)
    (hc1 : CollisionFreeOn H revealed
      (n.toFundingParams H).witnessScript.bytes) :
    revealed = (n.toFundingParams H).witnessScript.bytes

theorem constructed_determine_witnessScript
    (H : ByteArray → ByteArray) (n m : FundingNegotiation)
    (heq : (n.toFundingParams H).fundingScriptPubKey =
      (m.toFundingParams H).fundingScriptPubKey)
    (hc1 : CollisionFreeOn H (n.toFundingParams H).witnessScript.bytes
      (m.toFundingParams H).witnessScript.bytes) :
    (n.toFundingParams H).witnessScript.bytes =
      (m.toFundingParams H).witnessScript.bytes

theorem constructed_forward_satisfiable :
    ∃ (H : ByteArray → ByteArray) (n : FundingNegotiation),
      (∀ b : ByteArray, (H b).size = 32) ∧
      (n.toFundingParams H).WellFormed ∧
      FundingScriptHashLinked H (n.toFundingParams H)
```

Non-determination counterexample:

```lean
theorem acceptChannel_alone_does_not_determine_witnessScript :
    ∃ (m : AcceptChannel) (k₁ k₂ : PubKey),
      (m.toFundingNegotiation k₁ 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes ≠
        (m.toFundingNegotiation k₂ 0 ⟨0⟩
          ⟨⟨ByteArray.empty⟩⟩).witnessScript.bytes
```

The proof uses two concrete 33-byte keys (`pub33 0`, `pub33 1`) and inspects
byte offsets 2 and 36 of the 71-byte script, case-splitting on
`orderedFundingKeys_pair`. The offsets are the first byte of the first and
second serialized keys (`OP_2 <0x21> <33 bytes> <0x21> ...`: offset 2 and
36). `ByteArray` equality is not decidable in Lean (`ByteArray.decEq` is an
`@[extern]`), which is why the proof does not use `decide` on whole arrays.

## 3. Build result

Command (shared lock, single thread):

```bash
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Protocol.Handshake LnLean.Bitcoin.Funding \
    LnLean.Proofs.Bitcoin.FundingLinkTargets
```

Result:

```
✔ [16/16] Built LnLean.Proofs.Bitcoin.FundingLinkTargets (844ms)
Build completed successfully (16 jobs).
RC=0
```

Downstream sanity check (not part of the lane build, run because
`Handshake.lean` changed and `HandshakeProps` consumes it):

```bash
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Protocol.Peer LnLean.Proofs.Protocol.HandshakeProps
# Build completed successfully (14 jobs). RC=0
```

The full `lake build` was **not** run, per lane rules.

## 4. Axiom audit

`#print axioms` was run for every public theorem in the new module and the
principal new declarations in `Funding.lean` / `Handshake.lean`. All results
are subsets of `{propext, Quot.sound, Classical.choice}`; there is no
`sorryAx` and no lane-local axiom.

| Declaration | Axioms |
|---|---|
| `toFundingParams_hash_linked` | `propext` |
| `toFundingParams_hash_linked_sha256` | `propext` |
| `toFundingParams_witnessScriptHash_size` | `propext` |
| `toFundingParams_witnessScriptHash_size_sha256` | `propext` |
| `toFundingParams_scriptPubKey_eq_p2wsh` | `propext` |
| `witnessScript_bytes_eq_TwoOfTwoScriptBytes` | `propext` |
| `ofKeys_witnessScript_isTwoOfTwo` | `propext` |
| `toFundingParams_witnessScript_bytes_eq_TwoOfTwo` | `propext` |
| `fundingScriptPubKey_eq_p2wsh_ordered` | `propext` |
| `fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed` | `propext` |
| `witnessScriptHash_eq_hash_TwoOfTwo` | `propext` |
| `acceptChannel_funding_link` | `propext` |
| `acceptChannel_funding_link_sha256` | `propext` |
| `acceptChannel_funding_link_ordered` | `propext` |
| `toFundingOutput_scriptPubKey_eq_p2wsh` | `propext` |
| `fundingConfirmed_script_commits_constructed` | `propext` |
| `fundingConfirmed_script_commits_TwoOfTwo` | `propext` |
| `constructed_binds_twoOfTwo` | `propext`, `Quot.sound` |
| `constructed_binds_witnessScript` | `propext` |
| `constructed_determine_witnessScript` | `propext`, `Quot.sound` |
| `constructed_forward_satisfiable` | `propext`, `Quot.sound`, `Classical.choice` |
| `acceptChannel_alone_does_not_determine_witnessScript` | `propext`, `Quot.sound` |
| `FundingNegotiation.toFundingParams_witnessScriptHash` | `propext` |
| `FundingNegotiation.toFundingParams_fundingScriptPubKey` | `propext` |
| `FundingNegotiation.toFundingParams_witnessScriptHash_size` | `propext` |
| `FundingNegotiation.toFundingParams_wellFormed` | `propext` |
| `FundingScript.ofKeys_witnessScript_bytes` | `propext` |
| `FundingScript.ofKeys_witnessScript_eq_witnessScript` | `propext` |
| `FundingScript.ofKeys_witnessScript_eq_ordered_pair` | `propext` |
| `AcceptChannel.toFundingNegotiation_remoteFundingKey` | none |
| `AcceptChannel.toFundingNegotiation_localFundingKey` | none |
| `AcceptChannel.toFundingParams_witnessScriptHash` | `propext` |
| `acceptReceived_of_sendFundingCreated` | `propext` |
| `acceptReceived_of_recvAcceptChannel` | `propext` |

The two `AcceptChannel.toFundingNegotiation_*` projections are `rfl` and depend
on no axioms. The remaining `rfl` projections in `Funding.lean`
(`toFundingParams_fundingSatoshis`, etc.) are definitional and likewise
introduce no axiom.

## 5. Forbidden-construct scan

```bash
grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^[[:space:]]*axiom[[:space:]]' \
  LnLean/Protocol/Handshake.lean \
  LnLean/Bitcoin/Funding.lean \
  LnLean/Proofs/Bitcoin/FundingLinkTargets.lean
```

Result: no matches (exit status 1). The lane introduces no `axiom`,
`@[implemented_by]`, `unsafe`, `native_decide`, `sorry`, or `admit`.

## 6. What is proved, precisely

### 6.1 `L1-03` — the link is constructed, not assumed

- `FundingNegotiation` has no hash field. `toFundingParams H` stores
  `H n.witnessScript.bytes`, and `n.witnessScript` is
  `FundingScript.ofKeys` of the two keys. Therefore
  `toFundingParams_hash_linked H n` is `rfl`.
- `acceptChannel_funding_link_ordered` reads the remote key from
  `m.fundingPubKey` and returns the exact ordered P2WSH output
  `p2wsh (H (TwoOfTwoScriptBytes first second))`. No disjunction and no hash
  hypothesis.
- `fundingScriptPubKey_eq_p2wsh_twoOfTwo_constructed` recovers the existing
  `FundingScriptTargets.fundingScriptPubKey_eq_p2wsh_twoOfTwo` conclusion with
  its `FundingScriptHashLinked` hypothesis discharged.
- `fundingConfirmed_script_commits_constructed` shows any confirmed output of
  the constructed funding transaction has the literal P2WSH byte shape
  `OP_0 <0x20> H(script)`.
- `AcceptChannel.toFundingParams_witnessScriptHash` is the same fact at the
  `AcceptChannel` API boundary, and `acceptReceived_of_sendFundingCreated`
  proves the peer key is available before `funding_created` can be sent.

`L1-03` is therefore addressed **for the modelled handshake path**. It is not
addressed for an `open_channel` message, because the model has none: the
opener's fields are local parameters, not decoded wire data. The construction
also does not authenticate the key (see §7).

### 6.2 `L1-05` — finite C1 admission kept

The forward direction is definitional. The reverse direction is still
cryptographic and is not smuggled in:

- `constructed_binds_twoOfTwo` concludes `IsTwoOfTwoScript ... revealed` and
  `revealed.size = 71` **only** under
  `CollisionFreeOn H revealed p.witnessScript.bytes`, the finite pair-level
  admission `H x = H y → x = y`.
- `constructed_binds_witnessScript` and
  `constructed_determine_witnessScript` are the same contract at the
  hash/output level.
- No theorem assumes `∀ x y, H x = H y → x = y` on all byte strings, and none
  derives the 71-byte admission from C1's 32-byte injectivity. The prior
  `c1_32_does_not_bind_funding_witnessScripts` boundary remains intact.
- `constructed_forward_satisfiable` proves the forward bundle (32-byte output,
  `WellFormed`, hash link) is inhabited, so the construction is not vacuous.
  The reverse admission's satisfiability is already mechanised by
  `FundingScriptTargets.fundingScriptPair_assumptions_satisfiable`.

`L1-05` remains **open** as a cryptographic assumption: the lane narrows the
gap by adding the construction lemma for the actual revealed script, but the
reverse binding still needs the finite admission. This is the intended
outcome, not a regression.

## 7. Scope caveats

1. **`H` is abstract.** The forward construction holds for any
   `ByteArray → ByteArray`. The SHA-256 instance uses `PrimitiveModel.sha256`,
   which is the model's opaque interface. Nothing here proves that `M.sha256`
   is FIPS 180-4 SHA-256, and no width law is derived for an arbitrary `H`
   without the explicit hypothesis `∀ b, (H b).size = 32`.
2. **`PubKey.Valid` is length-only.** The well-formedness bridge uses the
   model's existing `Valid` predicate (33-byte key), not curve-point validity.
   That matches the rest of the model and the wire decoder's checks.
3. **No authentication, no C3, no Noise.** `accept_channel.funding_pubkey` is
   the key the peer *claims*. Binding that key to the signer is `PR-01` and is
   out of scope. `AcceptChannel` fields are length-checked, not
   signature-verified here.
4. **No `open_channel` message.** The model has no `open_channel`
   constructor, so `localFundingKey`, `fundingSatoshis`, `pushMsat`, and
   `temporaryChannelId` are explicit local arguments. Consequently
   `acceptChannel_alone_does_not_determine_witnessScript` is a real
   limitation, not a proof artefact: a single `accept_channel` record is
   compatible with distinct witness scripts.
5. **Reverse binding is conditional.** Without `CollisionFreeOn`, a revealed
   script with the same hash is not proved equal to the funding script. No
   global injectivity is claimed.
6. **No interpreter bridge.** This lane says nothing about script execution,
   sighash, or `OP_CHECKMULTISIG`; those are `L1-01`/`L1-07`/`MODEL-01`.
7. **No catalog/traceability edit.** The lane was forbidden from touching
   `Obligations.lean`/`Traceability.lean`; the recommended integration patch
   is in §8.

## 8. Integration steps (for the parent)

The lane changes are additive and compile on top of `79a92ce` with the current
other-lane worktree changes untouched.

1. **Root import.** Add the new proof module to `LnLean.lean` in the
   `LnLean.Proofs.Bitcoin` block (alphabetically after
   `FundingScriptTargets`):

   ```lean
   import LnLean.Proofs.Bitcoin.FundingLinkTargets
   ```

2. **Catalog target (`LN-L1-001`).** The current row points at the conditional
   disjunctive theorem. Recommended retarget to the ordered, constructed form:

   ```lean
   leanTarget :=
     "LnLean.Proofs.Bitcoin.FundingLinkTargets.fundingScriptPubKey_eq_p2wsh_ordered"
   ```

   and update the claim text to say the hash link is constructed from
   `FundingNegotiation`, the reverse direction keeps the finite
   `CollisionFreeOn` admission, and `H` is an abstract hash (with
   `M.sha256` as the model instance). If a handshake-facing target is
   preferred, use
   `LnLean.Proofs.Bitcoin.FundingLinkTargets.acceptChannel_funding_link_ordered`
   instead; it additionally identifies `remoteFundingKey = m.fundingPubKey`.

3. **Traceability.** Add a `TargetEntry` for the chosen target with module
   `LnLean.Proofs.Bitcoin.FundingLinkTargets`, and add the corresponding
   `ProvedEntry` whose declaration list names the target. If the catalog keeps
   both targets, list both declarations (the existing style supports
   semicolon-separated targets with parallel declaration lists). Add the module
   to the traceability module list near `LnLean.Proofs.Bitcoin.FundingScriptTargets`.

4. **Issue text.** Suggested `docs/OPEN-ISSUES.md` update for `L1-03`:
   *"The handshake path now constructs `witnessScriptHash = H(witnessScript.bytes)`
   in `FundingNegotiation.toFundingParams`; the link is `rfl` and
   `acceptChannel_funding_link_ordered` gives the exact ordered P2WSH output.
   `open_channel` decoding and key authentication remain out of scope."*
   For `L1-05`: *"The finite pair-level `CollisionFreeOn` admission is kept;
   `constructed_binds_twoOfTwo` is the constructed-script reverse form. No
   global or 71-byte injectivity is assumed."*

5. **No other edits.** `Funding.lean` and `Handshake.lean` only add
   declarations; existing signatures and semantics are unchanged. The new
   module imports `LnLean.Protocol.Handshake`,
   `LnLean.Proofs.Bitcoin.FundingScriptTargets`, and
   `LnLean.Crypto.Model`, so the root import order above is sufficient.

## 9. Reproduction

```bash
cd /home/ubuntu/ln-lean-repair

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Protocol.Handshake LnLean.Bitcoin.Funding \
    LnLean.Proofs.Bitcoin.FundingLinkTargets

grep -nE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^[[:space:]]*axiom[[:space:]]' \
  LnLean/Protocol/Handshake.lean \
  LnLean/Bitcoin/Funding.lean \
  LnLean/Proofs/Bitcoin/FundingLinkTargets.lean
```

The axiom audit was run from `/tmp/opencode/Axioms.lean` with
`lake env lean`; every declaration reported a subset of
`{propext, Quot.sound, Classical.choice}`.

## 10. Blockers

None for the assigned scope. Remaining gaps are deliberate boundaries:
`open_channel` decoding, key authentication/`PR-01`, the computational
reverse-direction admission (`L1-05`), and the interpreter bridge
(`L1-01`/`L1-07`).
