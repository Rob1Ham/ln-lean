# S10-L1-EC-DOMAIN — no fixed tag repairs `DigestBindsMod`

**Lane:** `S10-L1-EC-DOMAIN`
**Issues:** `L1-01`, `L1-07`
**Recommended catalog rows:** `LN-L1-001`, `LN-L1-004`
**Branch:** `repair/integrated`
**Launch HEAD:** `7988c93` (base `9158592`)
**Status:** complete; general tag impossibility proved, canonical-domain
positive repair proved, scoped build and axiom audit clean
**Owned files created:** `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean`,
`agents/reports/swarm10/S10-L1-EC-DOMAIN.md`
**Files edited outside the owned set:** none. No commit, push, root import,
catalog, traceability, audit, or docs edit. Other lanes' working-tree changes
are present and untouched.

---

## 1. Objective

Wave 9 (`EcdsaConcreteTargets`) reduced the concrete ECDSA seam to two exact
facts:

* `ResidueBinding vendorVerify` — `verifyImpl` binds only the reduced scalar
  `bytesToNatBE msg % n`, not the message bytes.
* `DigestBindsMod fundingTag` — the additional injectivity side condition
  needed by `residueBinding_vendor_funding_eq_of_digestBinds` to upgrade two
  accepted signatures to transaction equality.

Wave 9 proved `not_digestBindsMod_fundingTag` with the distinct 33-byte
messages `zeros 33` and `nBytes33`. The wave-10 question was whether a different
fixed tag can repair the interface.

This lane answers it: **no fixed tag can.** For every tag, the same two 33-byte
suffixes collide modulo `n`. The exact positive repair is a restricted message
domain (33-byte encodings whose value is already below `n`), not a new tag.

## 2. Answer in one paragraph

The missing arithmetic lemma was the concatenation law for the vendored
big-endian decoder:
`bytesToNatBE (a ++ b) = bytesToNatBE a * 256 ^ b.size + bytesToNatBE b`.
It is now proved from the fold accumulator law
`foldl step acc l = acc * 256 ^ length + foldl step 0 l`.
For every tag `tag`,
`bytesToNatBE (tag ++ zeros 33) % n = bytesToNatBE (tag ++ nBytes33) % n`:
the tag contributes the common offset `bytesToNatBE tag * 256 ^ 33`, while the
suffix values differ by exactly `n`. Since `zeros 33 ≠ nBytes33`, this yields
`not_digestBindsMod_any_tag : ∀ tag, ¬ DigestBindsMod tag` and
`no_digestBindsMod_anywhere : ¬ ∃ tag, DigestBindsMod tag`. The failure is not
specific to `fundingTag`, not a length artefact (both witnesses have size 33),
and not specific to this suffix pair: any equal-size suffixes whose values
differ by `n` collide under every tag (`tagged_modEq_of_value_add_n`).
The conditional extraction forms are preserved for an arbitrary tag, but their
`DigestBindsMod` hypothesis is now proved empty. The faithful positive result is
`digestBindsModOn_canonicalOfSize`: on `CanonicalOfSize k` (`k`-byte encodings
with `bytesToNatBE m < n`), every tag **does** bind, for every `k`. The 33-byte
instance `digestBindsModOn_canonical33` matches the wave-9 collision pair, and
the 32-byte instance `digestBindsModOn_canonical32` is the natural typed-digest
domain. The domain is non-vacuous (`canonical33_zeros`, `canonical32_zeros`)
and excludes exactly the bad `nBytes33` suffix (`not_canonical33_nBytes33`).
This gives the conditional funding extraction
`residueBinding_vendor_funding_eq_of_canonical33` without any new tag.

## 3. Exact results

Namespace: `LnLean.Proofs.Bitcoin.EcdsaDomainTargets`
File: `LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean` (486 lines)
Imports: `LnLean.Proofs.Bitcoin.EcdsaConcreteTargets` only.

### 3.1 Append arithmetic and fixed-length injectivity

| Theorem / def | Line | Statement |
|---|---:|---|
| `bytesToNatBE_append` | 99 | `bytesToNatBE (a ++ b) = bytesToNatBE a * 256 ^ b.size + bytesToNatBE b` |
| `bytesToNatBE_lt_pow_size` | 141 | `bytesToNatBE m < 256 ^ m.size` |
| `bytesToNatBE_injective_of_size_eq` | 210 | equal size + equal value ⇒ equal bytes |
| `zeros_size` | 227 | `(zeros k).size = k` |
| `bytesToNatBE_zeros` | 233 | `bytesToNatBE (zeros k) = 0` |
| `bytesToNatBE_append_zeros33` | 245 | appending `zeros 33` shifts the tag value by `256 ^ 33` |
| `bytesToNatBE_append_nBytes33` | 251 | appending `nBytes33` shifts by `256 ^ 33` and adds `n` |

The append lemma is the exact lemma wave 9 lacked. Fixed-length injectivity is
proved independently by induction on the byte list; it is needed only for the
positive canonical-domain theorem.

### 3.2 General tag impossibility (negative result)

| Theorem | Line | Statement |
|---|---:|---|
| `tagged_modEq_of_value_add_n` | 259 | equal-size suffixes with values differing by `n` collide under every tag |
| `tagged_zeros_nBytes33_modEq` | 269 | `bytesToNatBE (tag ++ zeros 33) % n = bytesToNatBE (tag ++ nBytes33) % n` |
| `not_digestBindsMod_any_tag` | 281 | `∀ tag : ByteArray, ¬ DigestBindsMod tag` |
| `no_digestBindsMod_anywhere` | 288 | `¬ ∃ tag : ByteArray, DigestBindsMod tag` |
| `digest_collision_witness_any_tag` | 294 | collision witness `⟨zeros 33, nBytes33⟩` for every tag |
| `not_digestBindsModOn33_any_tag` | 301 | the failure survives the full 33-byte fixed-length domain |
| `digestBindsMod_hypothesis_empty` | 338 | `DigestBindsMod tag ↔ False` |

This is a genuinely negative result: **no canonical tag repairs the raw-residue
interface.** It is not a claim that ECDSA is broken; the collision is in the
untyped `ByteArray → Nat % n` message representation, exactly as characterized
by wave 9.

### 3.3 Preserved conditional extraction forms

| Theorem | Line | Statement |
|---|---:|---|
| `residueBinding_vendor_eq_of_digestBinds_any_tag` | 319 | residue binding + `DigestBindsMod tag` + two accepted tagged messages ⇒ message equality |
| `vendorEcdsaContract_eq_of_digestBinds_any_tag` | 328 | the same under `VendorEcdsaContract` |
| `residueBinding_vendor_funding_eq_of_canonical33` | 453 | funding-domain extraction under residue binding + `Canonical33` |
| `vendorEcdsaContract_funding_eq_of_canonical33` | 465 | the same under `VendorEcdsaContract` |

The first two preserve the wave-9 conditional theorem shape verbatim, but
quantified over an arbitrary tag. Their side condition is now empty; the
canonical-domain forms are the non-vacuous replacements.

### 3.4 Positive canonical-domain repair (non-vacuous)

| Theorem / def | Line | Statement |
|---|---:|---|
| `CanonicalOfSize` | 352 | `m.size = k ∧ bytesToNatBE m < n` |
| `Canonical33` | 356 | `CanonicalOfSize 33` |
| `DigestBindsModOn` | 361 | `DigestBindsMod` restricted to an explicit message predicate |
| `n_pos` | 366 | `0 < n` |
| `canonical33_zeros` | 369 | `Canonical33 (zeros 33)` |
| `not_canonical33_nBytes33` | 377 | `¬ Canonical33 nBytes33` |
| `digestBindsModOn_canonicalOfSize` | 400 | for every tag and `k`, binding on the canonical `k`-byte domain |
| `digestBindsModOn_canonical33` | 428 | the 33-byte instance matching the collision pair |
| `CanonicalDigest32` | 434 | `CanonicalOfSize 32` |
| `digestBindsModOn_canonical32` | 438 | the natural 32-byte digest instance |
| `canonical32_zeros` | 443 | `CanonicalDigest32 (zeros 32)` |
| `digest_domain_dichotomy` | 478 | bundles full-domain negative, canonical-domain positive, and fixed-length-33 negative |

`Canonical33` means the 33-byte big-endian encoding is already a reduced
scalar (`< n`), i.e. a zero-prefixed 32-byte digest. The theorem is not a
singleton/vacuous domain: `zeros 33` is a member, and the bad collision side
`nBytes33` is excluded by its value bound exactly.

## 4. Why the proof is sharp and where the boundary moved

* The general collision is **tag-independent**, so the wave-9 question
  "is `fundingTag` the wrong tag?" is answered no.
* The collision pair has **equal length 33**, so the failure is not repaired by
  merely fixing the message length. `not_digestBindsModOn33_any_tag` records
  this.
* The general reduction `tagged_modEq_of_value_add_n` shows the failure is a
  property of any equal-size suffix pair whose big-endian values differ by
  `n`; it is not an artifact of the chosen all-zero / `nBytes33` pair.
* The positive theorem identifies the exact extra condition: the suffix value
  must be in `[0, n)`. Under that condition, modulo-`n` equality of the sums
  forces equality of the suffix values (`mod_add_cancel_of_lt`), and
  fixed-length injectivity forces equality of the byte strings.
* No `sorry`, no new axiom, no `native_decide`, no `unsafe`, no
  `@[implemented_by]`; no computation of a real signature was needed.

The remaining boundary is therefore: **a fixed tag does not help; a positive
`DigestBindsMod` for arbitrary transaction bytes is false.** A production
repair must either

1. restrict the transaction encoding to the canonical value-`< n` 33-byte
   domain (formalized here), or
2. move binding to a typed digest domain with an explicit computational
   hash/collision-resistance hypothesis (the CR-01 direction), rather than
   claiming byte-level injectivity of `bytesToNatBE · % n` on `ByteArray`.

## 5. Validation

Scoped build (exact command from the lane brief):

```
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.EcdsaDomainTargets
```

Result:

```
✔ [61/61] Built LnLean.Proofs.Bitcoin.EcdsaDomainTargets
Build completed successfully (61 jobs).
```

A direct `lake env lean LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean`
typecheck produced no output (no errors, no warnings).

**Axiom audit.** Scoped `#print axioms` over all 26 public theorems:

* audited: 26
* no-axiom theorems: 2 (`n_pos`, `not_canonical33_nBytes33`)
* axioms observed: exactly `propext`, `Quot.sound`, `Classical.choice`

No other axiom, including any project-local or cryptographic assumption, is
introduced by the module.

**Forbidden-token scan** over the owned Lean file:

```
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b|implemented_by' \
  LnLean/Proofs/Bitcoin/EcdsaDomainTargets.lean
```

Result: no matches (`NO_FORBIDDEN_TOKENS`).

**Public inventory:** 26 theorems, 4 public definitions (`CanonicalOfSize`,
`Canonical33`, `DigestBindsModOn`, `CanonicalDigest32`), 1 private fold step,
486 lines.

## 6. Catalog integration recommendation

Recommended for both `LN-L1-001` (funding output / concrete EC seam) and
`LN-L1-004` (`to_local` / concrete EC seam), since both rows currently carry the
same wave-9 ECDSA-boundary target list. Append to `leanTarget`:

```text
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsMod_any_tag
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.no_digestBindsMod_anywhere
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.not_digestBindsModOn33_any_tag
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical33
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.digestBindsModOn_canonical32
; LnLean.Proofs.Bitcoin.EcdsaDomainTargets.residueBinding_vendor_funding_eq_of_canonical33
```

Recommended claim-text edit for both rows: replace the trailing

```text
byte-level binding requires an explicit canonical `DigestBindsMod` domain.
```

with

```text
no fixed tag satisfies `DigestBindsMod` (`not_digestBindsMod_any_tag`);
the exact repair is a canonical fixed-size value-`< n` domain
(`digestBindsModOn_canonicalOfSize`), with the 33-byte suffix instance
(`digestBindsModOn_canonical33`) and the 32-byte digest instance
(`digestBindsModOn_canonical32`), which yield the conditional funding
extraction `residueBinding_vendor_funding_eq_of_canonical33`.
```

Parent integration steps (not performed by this lane): add
`import LnLean.Proofs.Bitcoin.EcdsaDomainTargets` to `LnLean.lean`, append the
six targets above to both catalog rows, and add the 26 public theorem names (or
the six headline names) to the axiom-audit list. No new obligation row is
needed; this is evidence within `LN-L1-001` / `LN-L1-004`, not a new claim of
unconditional spendability.

**Suggested headline targets:**

* `LN-L1-001` / `LN-L1-004` negative boundary:
  `EcdsaDomainTargets.not_digestBindsMod_any_tag`
* `LN-L1-001` / `LN-L1-004` positive canonical repair:
  `EcdsaDomainTargets.digestBindsModOn_canonical33` (33-byte suffix instance)
  and `EcdsaDomainTargets.digestBindsModOn_canonical32` (32-byte digest
  instance)
* `LN-L1-001` / `LN-L1-004` bundled domain statement:
  `EcdsaDomainTargets.digest_domain_dichotomy`

## 7. Remaining boundary

* **No** unconditional ECDSA or consensus-security claim. The module does not
  prove `EufCma vendorVerify`, does not exhibit an accepted signature, and does
  not claim a concrete non-vacuous vendor verifier. Those wave-9 boundaries are
  unchanged.
* `DigestBindsMod` is **false for every tag** on `ByteArray`; the wave-9
  conditional extraction theorem remains available but has no instance at the
  untyped interface.
* The positive canonical domain is a *restricted message domain*, not a new
  wire or tag. It assumes the transaction encoding is a 33-byte big-endian
  value below `n`; applying it to real transactions requires that encoding
  discipline (or the typed-digest/hash-resistance alternative).
* Key binding (`KeyBinding vendorVerify`) and EUF-CMA remain independent
  hypotheses, exactly as in wave 9.
* Computational collision resistance of a real hash function is outside this
  algebraic module (`CR-01`); no reduction is claimed.

## 8. What is not claimed

This report does not claim that ECDSA is forgeable, that the vendored verifier
is insecure, or that any real transaction pair collides. It proves that the
untyped residue interface cannot bind bytes for any fixed tag, and that the
canonical value-reduced 33-byte domain is the exact algebraic repair available
without a computational hash assumption.
