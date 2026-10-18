# CR-RETARGET — crypto catalog retarget audit (`LN-CR-001/002/003`)

**Agent:** CR-RETARGET  
**Date:** 2026-10-18  
**Worktree:** `/home/ubuntu/ln-lean-repair`  
**Branch:** `repair/integrated` @ `0caec3d`  
**Owned files:** `LnLean/Proofs/CryptoTargets.lean`, `agents/reports/CR-RETARGET.md`  
**Scope:** audit the three crypto catalog targets and add faithful standalone
candidate declarations. No catalog edit, no commit, no push.

**Status: complete.** Three candidate contracts are proved in the new module.
All three need their English claims tightened before promotion. For
`LN-CR-001` and `LN-CR-003` the narrowed claims are fully captured by the new
contracts; for `LN-CR-002` the C3-conditional binding half is captured, while
the literal "honest signatures verify" direction has an exact model blocker.

---

## 1. Summary

| Row | Current target | Why it cannot be promoted | Recommended target | Faithful status |
|---|---|---|---|---|
| `LN-CR-001` | `LnLean.Crypto.Hash.sha256` | `sha256` is a field of `PrimitiveModel`, not a declaration in this namespace | `LnLean.Crypto.Hash.paymentHash_sha256_contract` | Proved, conditional on C1; output-ness is structural for constructed/opened hashes |
| `LN-CR-002` | `LnLean.Crypto.Sig.ecdsaVerify` | `ecdsaVerify` is a field of `PrimitiveModel`, not a declaration in this namespace | `LnLean.Crypto.Sig.commitmentSig_contract` | Proved C3-conditional message binding and domain separation; literal verification needs `SigningCompleteness` |
| `LN-CR-003` | `LnLean.Crypto.Hash.hmacSha256` | `hmacSha256` is a field of `PrimitiveModel`, not a declaration in this namespace | `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn` | Proved structural 32-byte width plus finite C8 `HmacBindsOn`; global PRF is false |

No row is promotable by changing only the target string while keeping the old
English wording. The catalog claim text also needs the qualifications in §5.

---

## 2. Exact audit of the old targets

The three names are fields of the structure in `LnLean/Crypto/Model.lean`:

```lean
structure PrimitiveModel where
  sha256 : ByteArray → ByteArray
  ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
  hmacSha256 : ByteArray → ByteArray → ByteArray
  ...
```

`LnLean/Crypto/Hash.lean` and `LnLean/Crypto/Sig.lean` use only the namespace
`LnLean.Crypto`; neither defines a namespace `LnLean.Crypto.Hash` or
`LnLean.Crypto.Sig`. The exact Lean queries fail:

```text
#check LnLean.Crypto.Hash.sha256
error: unknown identifier `LnLean.Crypto.Hash.sha256`

#check LnLean.Crypto.Sig.ecdsaVerify
error: unknown identifier `LnLean.Crypto.Sig.ecdsaVerify`

#check LnLean.Crypto.Hash.hmacSha256
error: unknown identifier `LnLean.Crypto.Hash.hmacSha256`
```

The fields themselves do exist:

```text
LnLean.Crypto.PrimitiveModel.sha256 (self : LnLean.Crypto.PrimitiveModel) :
  ByteArray → ByteArray

LnLean.Crypto.PrimitiveModel.ecdsaVerify (self : LnLean.Crypto.PrimitiveModel) :
  LnLean.PubKey → ByteArray → LnLean.EcdsaSig → Bool

LnLean.Crypto.PrimitiveModel.hmacSha256 (self : LnLean.Crypto.PrimitiveModel) :
  ByteArray → ByteArray → ByteArray
```

`scripts/check-catalog.py --allow-planned` currently lists all three as
`PLANNED` unresolved targets. This lane did not edit `Obligations.lean`, so the
catalog still shows them that way.

---

## 3. Candidate declarations

The new module is `LnLean/Proofs/CryptoTargets.lean`. Its exact declarations
resolve as `theorem` declarations with no `sorry` (verified with the same
source-level declaration map used by `scripts/check-catalog.py`):

```text
LnLean.Crypto.Hash.paymentHash_sha256_contract
  -> theorem, LnLean.Proofs.CryptoTargets:88, has_sorry=False
LnLean.Crypto.Hash.paymentHash_opensTo_unique
  -> theorem, LnLean.Proofs.CryptoTargets:116, has_sorry=False
LnLean.Crypto.Hash.paymentHash_sha256_distinct
  -> theorem, LnLean.Proofs.CryptoTargets:125, has_sorry=False
LnLean.Crypto.Sig.commitmentSig_contract
  -> theorem, LnLean.Proofs.CryptoTargets:157, has_sorry=False
LnLean.Crypto.Sig.commitmentSig_binds_message
  -> theorem, LnLean.Proofs.CryptoTargets:183, has_sorry=False
LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn
  -> theorem, LnLean.Proofs.CryptoTargets:210, has_sorry=False
```

### 3.1 `LN-CR-001` — SHA-256

**Primary candidate:** `LnLean.Crypto.Hash.paymentHash_sha256_contract`

```text
#check LnLean.Crypto.Hash.paymentHash_sha256_contract
LnLean.Crypto.Hash.paymentHash_sha256_contract (M : LnLean.Crypto.PrimitiveModel)
  (hc : LnLean.Crypto.CollisionResistant M.sha256) :
  (∀ (pre : LnLean.Preimage), (M.paymentHashOf pre).bytes = M.sha256 pre.bytes) ∧
    (∀ {ph : LnLean.PaymentHash} {pre : LnLean.Preimage},
      LnLean.Crypto.opensTo M ph pre → ∃ b, M.sha256 b = ph.bytes) ∧
      (∀ {ph : LnLean.PaymentHash} {p q : LnLean.Preimage},
          LnLean.Crypto.opensTo M ph p → LnLean.Crypto.opensTo M ph q →
          p.Valid → q.Valid → p = q) ∧
        ∀ {p q : LnLean.Preimage},
          p.Valid → q.Valid → M.paymentHashOf p = M.paymentHashOf q → p = q
```

`#print axioms`:

```text
'LnLean.Crypto.Hash.paymentHash_sha256_contract' depends on axioms: [propext]
```

Interpretation:

1. Every canonical payment hash is literally the SHA-256 image of its
   preimage. This is the structural output-ness half and needs no C1.
2. Every hash lock that some preimage opens is in the range of `M.sha256`.
   This is also structural.
3. Two valid 32-byte preimages that open the same payment hash are equal
   (the C1-conditional commitment property).
4. Equal canonical payment hashes of valid preimages imply equal preimages
   (the C1-conditional commitment property).

The theorem deliberately does not quantify over an arbitrary `PaymentHash`.
The model has no range invariant on `PaymentHash`, so that stronger universal
reading is false; see §5.1.

**Alternative atomic candidates** (both proved in the same module):

```text
#check LnLean.Crypto.Hash.paymentHash_opensTo_unique
LnLean.Crypto.Hash.paymentHash_opensTo_unique (M : LnLean.Crypto.PrimitiveModel)
  (hc : LnLean.Crypto.CollisionResistant M.sha256)
  {ph : LnLean.PaymentHash} {p q : LnLean.Preimage}
  (hp : LnLean.Crypto.opensTo M ph p) (hq : LnLean.Crypto.opensTo M ph q)
  (hpv : p.Valid) (hqv : q.Valid) : p = q
```

```text
#check LnLean.Crypto.Hash.paymentHash_sha256_distinct
LnLean.Crypto.Hash.paymentHash_sha256_distinct (M : LnLean.Crypto.PrimitiveModel)
  (hc : LnLean.Crypto.CollisionResistant M.sha256)
  {p q : LnLean.Preimage} (hp : p.Valid) (hq : q.Valid) (hne : p ≠ q) :
  M.paymentHashOf p ≠ M.paymentHashOf q
```

These are intentionally atomic forms: the first is the hash-lock uniqueness
statement, the second is its contrapositive for distinct preimages. The primary
bundled contract is the recommended catalog target because it records both
output-ness and commitment in one theorem.

### 3.2 `LN-CR-002` — ECDSA

**Primary candidate:** `LnLean.Crypto.Sig.commitmentSig_contract`

```text
#check LnLean.Crypto.Sig.commitmentSig_contract
LnLean.Crypto.Sig.commitmentSig_contract (M : LnLean.Crypto.PrimitiveModel)
  (h : LnLean.Crypto.EufCma M.ecdsaVerify) (pk : LnLean.PubKey)
  (sig : LnLean.EcdsaSig) :
  (∀ {m₁ m₂ : ByteArray},
      LnLean.Crypto.verifyCommitment M pk m₁ sig = true →
      LnLean.Crypto.verifyCommitment M pk m₂ sig = true → m₁ = m₂) ∧
    (∀ {m : ByteArray},
        LnLean.Crypto.verifyCommitment M pk m sig = true →
        LnLean.Crypto.verifyFunding M pk m sig = false) ∧
      ∀ {m : ByteArray},
        LnLean.Crypto.verifyCommitment M pk m sig = true →
        LnLean.Crypto.verifyClose M pk m sig = false
```

`#print axioms`:

```text
'LnLean.Crypto.Sig.commitmentSig_contract' depends on axioms: [propext, Quot.sound]
```

Interpretation: for a fixed public key and signature, commitment-domain
acceptance determines the untagged message uniquely, and the same signature
cannot also verify in the funding or close domain for that message. This is
exactly the C3 (`EufCma M.ecdsaVerify`) consequence used by the protocol.
`pk` is an explicit parameter; at the channel level it is instantiated with
`c.remoteEndpoint.fundingPubKey` (see
`LnLean.Proofs.WaveE.E06.counterpartyFundingKey`).

**Alternative atomic candidate:**

```text
#check LnLean.Crypto.Sig.commitmentSig_binds_message
LnLean.Crypto.Sig.commitmentSig_binds_message (M : LnLean.Crypto.PrimitiveModel)
  (h : LnLean.Crypto.EufCma M.ecdsaVerify)
  {pk : LnLean.PubKey} {m₁ m₂ : ByteArray} {sig : LnLean.EcdsaSig}
  (h₁ : LnLean.Crypto.verifyCommitment M pk m₁ sig = true)
  (h₂ : LnLean.Crypto.verifyCommitment M pk m₂ sig = true) : m₁ = m₂
```

This atomic form is a thin restatement of the existing
`LnLean.Crypto.verifyCommitment_message_bound`; it is included so the catalog
can use a name in the `LnLean.Crypto.Sig` namespace if desired. The primary
bundled contract is the stronger recommendation because it also records
domain separation.

### 3.3 `LN-CR-003` — HMAC-SHA256

**Primary candidate:** `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn`

```text
#check LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn
LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn (M : LnLean.Crypto.PrimitiveModel)
  {mu : ByteArray} {msgs : List ByteArray}
  (hb : LnLean.Proofs.WaveD.D07.HmacBindsOn M.hmacSha256 mu msgs)
  (hopPayloads associatedData : ByteArray)
  (hmem : hopPayloads ++ associatedData ∈ msgs) :
  (LnLean.Proofs.WaveD.D07.onionHmacTag M mu hopPayloads associatedData).size = 32 ∧
    ∀ (hopPayloads' : ByteArray),
      hopPayloads' ++ associatedData ∈ msgs →
        LnLean.Proofs.WaveD.D07.onionHmacTag M mu hopPayloads' associatedData =
            LnLean.Proofs.WaveD.D07.onionHmacTag M mu hopPayloads associatedData →
          hopPayloads' = hopPayloads
```

`#print axioms`:

```text
'LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn' depends on axioms: [propext, Quot.sound]
```

Interpretation: the BOLT 4 tag is a 32-byte HMAC-SHA256 value, and under the
finite-execution C8 admission `HmacBindsOn M.hmacSha256 mu msgs` an authentic
tag determines the `hop_payloads` value uniquely among the messages of that
execution (with associated data held fixed). This is the faithful finite
property, not a global PRF assertion.

The C8 predicate and its negative boundary are exactly the existing D07
declarations:

```text
#check LnLean.Proofs.WaveD.D07.HmacBindsOn
LnLean.Proofs.WaveD.D07.HmacBindsOn (hmac : ByteArray → ByteArray → ByteArray)
  (mu : ByteArray) (msgs : List ByteArray) : Prop

#check LnLean.Proofs.WaveD.D07.hmacPrf_vacuous
LnLean.Proofs.WaveD.D07.hmacPrf_vacuous (M : LnLean.Crypto.PrimitiveModel)
  (k : ByteArray) : ¬LnLean.Crypto.HmacPrf M.hmacSha256

#check LnLean.Proofs.WaveD.D07.hmacBindsOn_singleton
LnLean.Proofs.WaveD.D07.hmacBindsOn_singleton
  (hmac : ByteArray → ByteArray → ByteArray) (mu m : ByteArray) :
  LnLean.Proofs.WaveD.D07.HmacBindsOn hmac mu [m]
```

`hmacBindsOn_singleton` shows the finite contract is satisfiable without any
cryptographic assumption; `hmacPrf_vacuous` shows the global form is not.

---

## 4. Existing faithful material (fallbacks)

If the parent prefers not to depend on the new module, these existing
declarations are also exact and faithful:

| Row | Existing target | Exact signature summary |
|---|---|---|
| `LN-CR-001` | `LnLean.Crypto.paymentHash_commits` | `(hc : CollisionResistant M.sha256) → p.Valid → q.Valid → M.paymentHashOf p = M.paymentHashOf q → p = q` |
| `LN-CR-001` | `LnLean.Crypto.preimage_unique` | `(hc : CollisionResistant M.sha256) → opensTo M ph p → opensTo M ph q → p.Valid → q.Valid → p = q` |
| `LN-CR-001` | `LnLean.Proofs.WaveD.D05.waveD_d05_paymentHashOf_commits` | same as `paymentHash_commits` |
| `LN-CR-002` | `LnLean.Crypto.verifyCommitment_message_bound` | `(h : EufCma M.ecdsaVerify) → verifyCommitment … = true → verifyCommitment … = true → m₁ = m₂` |
| `LN-CR-002` | `LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_sig_binds_digest` | channel-level counterparty-key form, C3-conditional |
| `LN-CR-003` | `LnLean.Proofs.WaveD.D07.waveD_d07_onionHmacTag_size_eq_32` | unconditional 32-byte width |
| `LN-CR-003` | `LnLean.Proofs.WaveD.D07.waveD_d07_onionHmacTag_payloads_unique` | C8-conditional payload uniqueness |

The new module's value is that it puts one contract per catalog row in the
namespace named by the old target, with the exact qualification needed for the
catalog wording.

---

## 5. Per-row verdict and exact blockers

### 5.1 `LN-CR-001` — retarget after narrowing the claim; universal reading blocked

**Recommended target:** `LnLean.Crypto.Hash.paymentHash_sha256_contract`  
**Recommended status:** `proved` only with the clarified claim below; otherwise
leave `statementOnly` and record the range gap.

Faithful claim wording:

> Constructed and opened payment hashes are SHA-256 outputs. Under assumption
> C1 (collision resistance on 32-byte preimages), a payment hash commits to at
> most one valid 32-byte preimage.

The literal universal reading "every `PaymentHash` value is a SHA-256 output"
is false in the model, and C1 does not repair it:

```text
#check LnLean.Proofs.WaveD.D05.waveD_d05_wellFormed_message_with_non_output_hash
LnLean.Proofs.WaveD.D05.waveD_d05_wellFormed_message_with_non_output_hash
  (M : LnLean.Crypto.PrimitiveModel) :
  ∃ m,
    LnLean.Protocol.wellFormed (LnLean.Protocol.Msg.updateAddHtlc m) ∧
      ¬m.paymentHash.Valid ∧ ∀ (b : ByteArray), M.sha256 b ≠ m.paymentHash.bytes
```

Blockers:

* `PaymentHash` is a bare `ByteArray` wrapper with no range invariant.
* `Protocol.wellFormed` checks wire shape but not that the payment-hash bytes
  are in `range M.sha256` (and not even that they are 32 bytes). D05 constructs
  a well-formed `update_add_htlc` with a 33-byte hash outside the range.
* The old global preimage-resistance idea is not a field of `PrimitiveModel`
  and is refuted for any 32-byte-output hash:

```text
#check LnLean.Proofs.Crypto.preimageResistant_vacuous
LnLean.Proofs.Crypto.preimageResistant_vacuous (M : LnLean.Crypto.PrimitiveModel) :
  ¬LnLean.Crypto.PreimageResistant M.sha256
```

Therefore the row cannot honestly be promoted as "all payment hashes are
SHA-256 outputs." The new contract is the strongest faithful standalone
statement available without adding a range invariant to the protocol model.

### 5.2 `LN-CR-002` — retarget for C3 binding; literal verification blocked

**Recommended target:** `LnLean.Crypto.Sig.commitmentSig_contract`  
**Recommended status:** `proved` only with the clarified claim below.

Faithful claim wording:

> Under assumption C3 (`EufCma M.ecdsaVerify`), a commitment-domain signature
> accepted under a given public key determines a unique commitment sighash and
> cannot be replayed as a funding- or close-domain signature for that message.

Exact blockers for the literal wording "commitment signatures verify under the
counterparty funding key":

1. **No signing operation or completeness law.** `PrimitiveModel` contains no
   `ecdsaSign`, and no field says that a signature produced by the counterparty
   is accepted by `ecdsaVerify`. The existing faithful positive direction is
   conditional on an explicit law:

```text
#check LnLean.Proofs.WaveE.E06.SigningCompleteness
LnLean.Proofs.WaveE.E06.SigningCompleteness (M : LnLean.Crypto.PrimitiveModel)
  (sign : LnLean.PubKey → ByteArray → LnLean.EcdsaSig) : Prop

#check LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_verifies_of_signing
LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_verifies_of_signing
  (M : LnLean.Crypto.PrimitiveModel)
  (sign : LnLean.PubKey → ByteArray → LnLean.EcdsaSig)
  (hsign : LnLean.Proofs.WaveE.E06.SigningCompleteness M sign)
  (c : LnLean.Channel.Channel) (sighash : ByteArray) :
  LnLean.Proofs.WaveE.E06.verifyCounterpartyCommitment M c sighash
      (sign (LnLean.Proofs.WaveE.E06.counterpartyFundingKey c)
        (LnLean.Crypto.commitmentTag ++ sighash)) = true
```

2. **C3 does not bind a signature to a key.** `EufCma` quantifies over a key but
   only forces message equality; the same `(message, signature)` may verify
   under two keys. Key attribution therefore needs the explicit `KeyBinding`
   hypothesis, and E06 proves C3 does not imply it:

```text
#check LnLean.Proofs.WaveE.E06.KeyBinding
LnLean.Proofs.WaveE.E06.KeyBinding
  (verify : LnLean.PubKey → ByteArray → LnLean.EcdsaSig → Bool) : Prop

#check LnLean.Proofs.WaveE.E06.waveE_e06_eufCma_not_keyBinding
LnLean.Proofs.WaveE.E06.waveE_e06_eufCma_not_keyBinding (d₀ : ByteArray) :
  ¬LnLean.Proofs.WaveE.E06.KeyBinding
    (LnLean.Proofs.WaveE.E06.waveE_e06_single_digest_verify d₀)
```

If the parent wants the channel-level "counterparty funding key" wording, the
best existing target is
`LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_sig_binds_digest`:

```text
#check LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_sig_binds_digest
LnLean.Proofs.WaveE.E06.waveE_e06_counterparty_commitment_sig_binds_digest
  (M : LnLean.Crypto.PrimitiveModel) (c : LnLean.Channel.Channel)
  {sighash₁ sighash₂ : ByteArray} {sig : LnLean.EcdsaSig}
  (h₁ : LnLean.Proofs.WaveE.E06.verifyCounterpartyCommitment M c sighash₁ sig = true)
  (h₂ : LnLean.Proofs.WaveE.E06.verifyCounterpartyCommitment M c sighash₂ sig = true) :
  sighash₁ = sighash₂
```

That theorem is C3-conditional binding under `counterpartyFundingKey`; it is
not a proof that honest signatures verify, and it still does not give key
attribution. It is a valid fallback if a channel-level target is required.

### 5.3 `LN-CR-003` — retarget to finite C8; global PRF claim blocked

**Recommended target:** `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn`  
**Recommended status:** `proved` only with the clarified claim below.

Faithful claim wording:

> An onion integrity check is a 32-byte HMAC-SHA256 tag. On the finite message
> set of one onion execution, assumption C8 (`HmacBindsOn M.hmacSha256 mu msgs`)
> makes equal tags under the same `mu` authenticate equal
> `hop_payloads || associated_data` values, hence a unique `hop_payloads` when
> associated data is fixed.

Exact blocker for the old "HMAC PRF" wording: the global contract
`HmacPrf M.hmacSha256` is false for every fixed key of a 32-byte-output HMAC:

```text
#check LnLean.Proofs.WaveD.D07.hmacPrf_vacuous
LnLean.Proofs.WaveD.D07.hmacPrf_vacuous (M : LnLean.Crypto.PrimitiveModel)
  (k : ByteArray) : ¬LnLean.Crypto.HmacPrf M.hmacSha256
```

C8 as used by the model is the finite predicate, not the global one. It is
satisfiable: `hmacBindsOn_singleton` proves a one-message execution, and
`hmacBindsOn_of_pairwise_tags` proves any finite set with pairwise distinct
tags. The new contract packages the structural 32-byte width together with the
finite binding consequence.

---

## 6. Build and verification

Commands used (one Lean process at a time, with the shared lock):

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake env lean LnLean/Proofs/CryptoTargets.lean
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.CryptoTargets
```

Results:

* `lake env lean LnLean/Proofs/CryptoTargets.lean` — **RC 0**, no diagnostics.
* `lake build LnLean.Proofs.CryptoTargets` — **RC 0**, `14/14` jobs built
  successfully (631 ms).
* No `sorry`, `admit`, `axiom` declaration, `native_decide`, `unsafe`, or
  `@[implemented_by]` in the new module. The only grep hit for the word
  "axiom" is prose in the module header.
* `scripts/check-catalog.py --allow-planned` still exits **RC 0** and still
  lists the three old crypto targets as `PLANNED`; the catalog itself was not
  edited by this lane and remains **29 proved / 19 statementOnly**.

`#print axioms` results for all new candidate declarations:

```text
'LnLean.Crypto.Hash.paymentHash_sha256_contract' depends on axioms: [propext]
'LnLean.Crypto.Hash.paymentHash_opensTo_unique' depends on axioms: [propext]
'LnLean.Crypto.Hash.paymentHash_sha256_distinct' depends on axioms: [propext]
'LnLean.Crypto.Sig.commitmentSig_contract' depends on axioms: [propext, Quot.sound]
'LnLean.Crypto.Sig.commitmentSig_binds_message' depends on axioms: [propext, Quot.sound]
'LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn' depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are the standard Lean axioms used by `ByteArray`
extensionality/cancellation; there is no `sorryAx` and no project-specific
axiom.

Worktree hygiene: the only files authored by this lane are the two owned files.
`git status --short` shows them as untracked and shows other lanes' concurrent
tracked/untracked work; no tracked file was modified by this lane. No commit or
push was made.

---

## 7. Integration note

`LnLean/Proofs/CryptoTargets.lean` is intentionally not added to `LnLean.lean`
by this lane (root imports are out of scope). If the parent retargets the
catalog and wants the module in the aggregate `LnLean` build, run
`scripts/regen-root.sh` or add the import explicitly. The source-level catalog
checker already sees the new declarations without a root import.

The parent's decision is therefore:

1. **`LN-CR-001`**: retarget to
   `LnLean.Crypto.Hash.paymentHash_sha256_contract` and amend the claim to
   "constructed/opened hashes" plus the C1 commitment reading, or keep it
   `statementOnly` if the universal wording must remain.
2. **`LN-CR-002`**: retarget to
   `LnLean.Crypto.Sig.commitmentSig_contract` for C3-conditional binding, or
   use the E06 counterparty-key binding theorem; do not mark literal
   "honest signatures verify" as proved without `SigningCompleteness`.
3. **`LN-CR-003`**: retarget to
   `LnLean.Crypto.Hash.onionHmacTag_size_and_bindsOn` and replace "HMAC PRF"
   with the finite C8 `HmacBindsOn` wording; the global PRF claim is refuted.
