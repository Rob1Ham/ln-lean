# Computational-security limits for C1, C3, and C8

**Status:** limits document and interface, not a reduction.
**Lane:** `S5-SEC-LIMITS` (`CR-01`, `SEC-01`).
**Lean module:** `LnLean/Proofs/Security/SecurityGameTargets.lean`.
**Related documents:** `docs/ASSUMPTIONS.md` §1, `docs/HMAC-LIMITS.md`,
`docs/OPEN-ISSUES.md` (`CR-01`, `SEC-01`), `docs/THEOREM-INDEX.md`.

This document states exactly what the current Lightning model assumes about
SHA-256 (C1), secp256k1 ECDSA (C3), and HMAC-SHA256 (C8), what it proves about
those assumptions, and what a game-based computational-security reduction would
have to add. It does **not** claim a reduction, an advantage bound for the
protocol, or computational security of Lightning.

The Lean module accompanying this document is deliberately an interface plus
algebra. It contains:

* a finite game skeleton and an event-level simulation record, with the one
  implication that is purely logical (event security transfers across a
  simulation);
* an advantage record and an advantage-reduction record whose `tight` field is
  the accounting inequality a cryptographic reduction would have to prove;
* the conventional `q²/2^λ` and `q/2^λ` bounds as `Rat`-valued definitions and
  an `AssumedBound` record whose only numeric content is a hypothesis;
* proofs of the exact algebraic facts the current model supports (no 32-byte
  SHA-256 collision under C1, no ECDSA message-binding failure under C3, no
  finite-execution HMAC tag collision under C8);
* a negative theorem showing that the event-level game alone does not determine
  an advantage: the same secure game admits advantage zero and advantage one.

No theorem in the module bounds the success probability of any concrete
adversary. `CR-01` and `SEC-01` remain open.

---

## 1. Summary of the position

| Question | Current answer |
|---|---|
| Does the tree prove SHA-256 collision resistance? | No. `CollisionResistant M.sha256` is an explicit field of `PrimitiveModel`; the tree proves consequences conditional on it. |
| Does the tree prove ECDSA EUF-CMA? | No. `EufCma M.ecdsaVerify` is an explicit field; its Lean meaning is message binding, not the EUF-CMA game. |
| Does the tree prove HMAC PRF security? | No. Global `HmacPrf` is refuted; C8 is the finite-execution predicate `HmacBindsOn`. |
| Is there a probability space? | No. |
| Is there a complexity/PPT notion? | No. |
| Is there a negligible-advantage statement? | Only the definition `Negligible`; closure and composition are not proved. |
| Is there a protocol-to-primitive reduction? | No. The module defines the record a reduction would inhabit and proves only its arithmetic consequence. |
| Are the algebraic assumptions the same as the computational assumptions? | No. They differ in strength and in kind; §6 lists the gap. |
| May a release claim "computationally secure Lightning"? | No. The defensible claim is model-level conditional safety under the listed assumptions. |

The short form:

> The catalog proves exact algebraic consequences of explicitly assumed
> primitive laws. It does not prove that those laws hold for SHA-256,
> secp256k1 ECDSA, or HMAC-SHA256, and it does not prove that an efficient
> adversary cannot break the protocol. A computational treatment needs a
> probability space, an adversary model, a reduction, and a negligible-loss
> analysis; none of those exist in this tree.

---

## 2. The exact algebraic model

### 2.1 Primitive record

`LnLean.Crypto.PrimitiveModel` (`LnLean/Crypto/Model.lean`) contains total
functions and the following properties as `Prop`-valued fields:

```lean
structure PrimitiveModel where
  sha256 : ByteArray → ByteArray
  hash160 : ByteArray → ByteArray
  ecdsaVerify : PubKey → ByteArray → EcdsaSig → Bool
  schnorrVerify : PubKey → ByteArray → SchnorrSig → Bool
  ecdh : ByteArray → PubKey → ByteArray
  hkdf : ByteArray → ByteArray → Nat → ByteArray
  aeadSeal : ByteArray → ByteArray → ByteArray → ByteArray
  aeadOpen : ByteArray → ByteArray → ByteArray → Option ByteArray
  hmacSha256 : ByteArray → ByteArray → ByteArray
  sha256_size : ∀ b, (sha256 b).size = 32
  hash160_size : ∀ b, (hash160 b).size = 20
  hmac_size : ∀ k m, (hmacSha256 k m).size = 32
  sha256_collisionResistant : CollisionResistant sha256
  ecdsa_eufCma : EufCma ecdsaVerify
  schnorr_eufCma : EufCma schnorrVerify
  aead_indCca : AeadIndCca aeadSeal aeadOpen
```

There is no `sign` operation, no key generation, no nonce, no probability, and
no oracle. A `PrimitiveModel` is an arbitrary total implementation satisfying
the fields; it is not SHA-256, secp256k1, or HMAC-SHA256.

### 2.2 C1 in Lean

```lean
abbrev CollisionResistant (H : ByteArray → ByteArray) : Prop :=
  ∀ x y : ByteArray, x.size = 32 → y.size = 32 → H x = H y → x = y
```

This is **injectivity on 32-byte inputs**, not the usual asymptotic collision
game and not injectivity on arbitrary byte strings. The global predicate
`PreimageResistant H := ∀ x y, H x = H y → x = y` is not a field: with
`sha256_size` it would inject all of `ByteArray` into the finite set of 32-byte
strings, which is refuted by
`LnLean.Proofs.Crypto.Sha256Props.preimageResistant_vacuous`.

The payment-hash path is:

```lean
def PrimitiveModel.paymentHashOf (M : PrimitiveModel) (pre : Preimage) : PaymentHash :=
  ⟨digest32 (M.sha256 pre.bytes)⟩

def opensTo (M : PrimitiveModel) (ph : PaymentHash) (pre : Preimage) : Prop :=
  digest32 (M.sha256 pre.bytes) = ph.bytes
```

`digest32` is the identity on 32-byte inputs (`digest32_of_size`), so the
canonical payment hash is literally a SHA-256 image. Under C1,
`preimage_unique` proves that two valid 32-byte preimages opening the same
payment hash are equal, and `paymentHash_commits` proves the corresponding
commitment form.

**Important domain restriction.** C1 says nothing about collisions on
71-byte witness scripts or on arbitrary BOLT 3 serialisations. `L1-05` records
that 32-byte payment-preimage collision resistance is not script injectivity;
the P2WSH direction uses a finite pair-level `CollisionFreeOn` admission.

### 2.3 C3 in Lean

```lean
abbrev EufCma {Sig : Type} (verify : PubKey → ByteArray → Sig → Bool) : Prop :=
  ∀ (pk : PubKey) (m₁ m₂ : ByteArray) (s : Sig),
    verify pk m₁ s = true → verify pk m₂ s = true → m₁ = m₂
```

This is **message binding for one key and one signature**: a single signature
cannot verify for two distinct messages. It is not the EUF-CMA game. In
particular:

* there is no signing oracle, no key generation, no adversary, and no
  forgery event;
* the predicate is satisfied vacuously by a verifier that always returns
  `false` (the concrete `safeParameters` in
  `LnLean/Proofs/PhaseC3/SecurityGame.lean` does exactly that);
* no theorem says an honest signature is accepted. That direction needs a
  signing function and a `SigningCompleteness` law, isolated in
  `LnLean/Proofs/WaveE/E06.lean`;
* no theorem attributes a signature to the counterparty key. That needs
  `KeyBinding`, which C3 does not imply; `WaveE.E06` proves the separation.

The domain tags are:

```lean
def verifyFunding (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (fundingTag ++ msg) sig

def verifyCommitment (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (commitmentTag ++ msg) sig

def verifyClose (M : PrimitiveModel) (pk : PubKey) (msg : ByteArray)
    (sig : EcdsaSig) : Bool :=
  M.ecdsaVerify pk (closeTag ++ msg) sig
```

Under `EufCma`, the existing theorems prove message uniqueness and pairwise
domain separation (`verifyFunding_not_verifyCommitment`, etc.). The tags are
compact model stand-ins, not the BOLT 3 sighash bytes.

### 2.4 C8 in Lean

Global HMAC injectivity is false for a 32-byte-output function:

```lean
abbrev HmacPrf (hmac : ByteArray → ByteArray → ByteArray) : Prop :=
  ∀ k m₁ m₂, hmac k m₁ = hmac k m₂ → m₁ = m₂
```

`LnLean.Proofs.WaveD.D07.hmacPrf_vacuous` proves `¬ HmacPrf M.hmacSha256` for
every fixed key. C8 is instead the finite-execution admission

```lean
def HmacBindsOn (hmac : ByteArray → ByteArray → ByteArray)
    (mu : ByteArray) (msgs : List ByteArray) : Prop :=
  ∀ m₁ ∈ msgs, ∀ m₂ ∈ msgs, hmac mu m₁ = hmac mu m₂ → m₁ = m₂
```

where `msgs` is the finite list of `hop_payloads ++ associated_data` values in
one onion execution. It is satisfiable without any cryptographic hardness:
`hmacBindsOn_of_pairwise_tags` holds whenever the tags in that finite list are
pairwise distinct, and `hmacBindsOn_singleton` holds for every HMAC on a
one-message execution.

C8 therefore says "no tag collision inside this execution", not "HMAC is a
PRF" and not "an adversary cannot forge a tag". `docs/HMAC-LIMITS.md` records
the same boundary.

---

## 3. Computational vocabulary that is not in the tree

A computational-security statement has the following ingredients. None of them
is formalised in `LnLean` today.

### 3.1 Game and advantage

For a game `G` with adversary `A`:

```text
Adv_G(A, λ) = Pr[G(A, λ) = 1]
```

`λ` is the security parameter. A primitive is secure when, for every
probabilistic polynomial-time (PPT) `A`,

```text
Adv_G(A, λ) ≤ negl(λ)
```

where `negl` means: for every positive polynomial `p`, there is `N` such that
for all `λ ≥ N`, `negl(λ) ≤ 1/p(λ)`.

The Lean module defines a definition-only version:

```lean
def Negligible (eps : Nat → Rat) : Prop :=
  ∀ c : Nat, 0 < c → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n ≤ (1 : Rat) / (c : Rat)
```

It does not prove closure under addition, composition, or game hopping. Those
are routine mathematical facts, but they are not available in a form this tree
can currently use.

### 3.2 Cost model

The module states bounds at an explicit cost model:

```lean
structure CostModel where
  securityParameter : Nat
  hashQueries : Nat
  signatureQueries : Nat
  hmacQueries : Nat
```

This is a query-count abstraction, not a runtime model. It cannot express
memory, parallel time, oracle programming, rewinding, or the cost of a
reduction. It is adequate for recording the shape of a conventional bound and
inadequate for claiming one.

### 3.3 Conventional bounds recorded by the module

```lean
def c1CollisionBound (c : CostModel) : Rat :=
  (c.hashQueries : Rat) * (c.hashQueries : Rat) / (2 : Rat) ^ c.securityParameter

def c1PreimageBound (c : CostModel) : Rat :=
  (c.hashQueries : Rat) / (2 : Rat) ^ c.securityParameter

def c3EufCmaBound (c : CostModel) : Rat :=
  (c.signatureQueries : Rat) / (2 : Rat) ^ c.securityParameter

def c8PrfBound (c : CostModel) : Rat :=
  (c.hmacQueries : Rat) / (2 : Rat) ^ c.securityParameter
```

These are **conventional heuristic shapes**, not theorems and not tight
constants. They are parameterised by `λ` and by query budgets. In particular:

* `c1CollisionBound` is the birthday bound `q²/2^λ`, not a proven bound on
  SHA-256;
* `c1PreimageBound` is the generic preimage bound `q/2^λ`; the Lean C1 field is
  collision resistance on 32-byte inputs, and the tree derives preimage
  uniqueness from that field rather than assuming a separate preimage bound;
* `c3EufCmaBound` is the generic-group-style `q_s/2^λ` shape, not a
  standard-model theorem about ECDSA;
* `c8PrfBound` is the generic PRF shape, not a theorem about HMAC's compression
  function and not a bound on the finite `HmacBindsOn` predicate.

The `AssumedBound` record stores a bound only together with its inequality:

```lean
structure AssumedBound where
  primitive : Primitive
  cost : CostModel
  advantage : Rat
  bound : Rat
  assumed : advantage ≤ bound
```

`no_assumedBound_of_violation` proves that a pair violating the inequality
cannot inhabit the record. That is a sanity check on the interface, not a
cryptographic result.

---

## 4. C1: SHA-256 collision and preimage limits

### 4.1 What the standard assumptions say

For a hash function `H` with `λ`-bit output:

| Property | Computational statement | Generic bound |
|---|---|---|
| Collision resistance | no PPT `A` outputs `x ≠ y` with `H(x) = H(y)` | `q²/2^λ` |
| Second-preimage resistance | given `x`, no PPT `A` outputs `y ≠ x` with `H(y) = H(x)` | `q/2^λ` |
| Preimage resistance | given `h`, no PPT `A` outputs `x` with `H(x) = h` | `q/2^λ` |

For SHA-256, `λ = 256`: collision security is about 128 bits and preimage
security about 256 bits under these generic bounds. The bounds are heuristic;
concrete constants and the treatment of the Merkle–Damgård construction are
outside the model.

### 4.2 What the Lean model gives

`CollisionResistant M.sha256` says there is **no** collision on 32-byte inputs.
That is stronger than computational collision resistance (which permits
collisions that are hard to find) and weaker than collision resistance on
arbitrary messages (it restricts the domain). It implies the uniqueness result
used by HTLCs:

```lean
theorem preimage_unique (M : PrimitiveModel) (h : CollisionResistant M.sha256)
    {ph : PaymentHash} {p q : Preimage}
    (hp : opensTo M ph p) (hq : opensTo M ph q)
    (hpv : p.Valid) (hqv : q.Valid) : p = q
```

The exact algebraic fact added by this lane is:

```lean
def Sha256Collision (M : PrimitiveModel) : Prop :=
  ∃ x y : ByteArray,
    x.size = 32 ∧ y.size = 32 ∧ x ≠ y ∧ M.sha256 x = M.sha256 y

theorem algebraic_c1_no_collision (M : PrimitiveModel)
    (h : CollisionResistant M.sha256) : ¬ Sha256Collision M
```

This theorem is unconditional in the model: it is a consequence of the field.
It does not say that real SHA-256 has no collision, and it does not bound the
probability that an adversary finds one.

### 4.3 What a C1 reduction would need

A protocol-level C1 reduction would have to:

1. define the collision game `CR_H` and the preimage game `PRE_H` with explicit
   sampling, adversary output, and win condition;
2. show that a protocol adversary producing two accepted commitments that
   require the same 32-byte payment hash but different preimages yields a
   collision (or a second preimage) with non-negligible probability;
3. account for the fact that the protocol may hide one preimage, may hash
   concatenations, and may use the hash outside the 32-byte payment-hash
   domain;
4. handle the L1-05 gap: a collision on 32-byte payment preimages does not give
   a collision on 71-byte witness scripts, and the P2WSH binding is currently a
   finite `CollisionFreeOn` admission;
5. compose the collision bound with the rest of the protocol game without
   losing more than a negligible factor.

The Lean module can state steps 1 and 2 as a `Game` and an `EventReduction`,
and it can state the arithmetic of step 5 as `AdvantageReduction.bound`. It
cannot prove the extraction or the probability statement.

---

## 5. C3: ECDSA EUF-CMA and key binding limits

### 5.1 What the standard assumption says

The EUF-CMA game for a signature scheme `(KeyGen, Sign, Verify)`:

1. `(pk, sk) ← KeyGen(λ)`;
2. `A` receives `pk` and a signing oracle `Sign(sk, ·)`;
3. `A` wins if it outputs `(m*, σ*)` such that `Verify(pk, m*, σ*) = true` and
   `m*` was never queried.

ECDSA with a 256-bit group has a generic security level of about 128 bits. The
generic-group analyses (Nechaev/Shoup; Pointcheval–Stern; Brown) give
`q_s/2^128`-shaped bounds under idealised group assumptions. There is no
standard-model reduction from the discrete-logarithm problem for ECDSA in full
generality, and nonce bias, DER parsing, low-S normalisation, and
signature malleability are additional implementation-level concerns outside
the model.

### 5.2 What the Lean model gives

`EufCma M.ecdsaVerify` is message binding, not the EUF-CMA game. The exact
algebraic fact added by this lane is:

```lean
def EcdsaBindingFailure (M : PrimitiveModel) : Prop :=
  ∃ (pk : PubKey) (m₁ m₂ : ByteArray) (sig : EcdsaSig),
    m₁ ≠ m₂ ∧ M.ecdsaVerify pk m₁ sig = true ∧
      M.ecdsaVerify pk m₂ sig = true

theorem algebraic_c3_no_binding_failure (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) : ¬ EcdsaBindingFailure M
```

Three gaps are load-bearing:

1. **No signing correctness.** A verifier that always rejects satisfies
   `EufCma` vacuously. The existing `safeParameters` instance uses
   `verify := fun _ _ _ => false`. Protocol theorems that need an honest
   signature to be accepted must add `SigningCompleteness` (see `WaveE.E06`);
   without it, "C3 holds" is not a security claim.
2. **No key binding.** `EufCma` is indexed by a public key. It does not say
   that the key used to verify is the counterparty's key, nor that the
   counterparty knows the secret key. `WaveE.E06` proves that C3 does not imply
   the `KeyBinding` hypothesis. `PR-01` remains open.
3. **No forking/extraction.** The protocol's bad event is not literally "a
   forgery". A real reduction must show that an accepted signature on a
   message the honest party never signed yields an EUF-CMA forgery, or that a
   signature accepted for two distinct messages yields a message-binding break
   with non-negligible probability. The latter is not a direct consequence of
   the EUF-CMA game (ECDSA signatures are malleable and not unique), so it
   needs a separate argument or a unique-signature assumption.

### 5.3 What a C3 reduction would need

1. an explicit `KeyGen`, `Sign`, `Verify` model and a correctness theorem;
2. an EUF-CMA game with a signing oracle, including the exact message domain
   (BOLT 3 sighash bytes, not an abstract tagged byte string);
3. a key-registration/key-binding game for `funding_pubkey`, or an
   authenticated-key assumption;
4. an extraction argument from the protocol bad event to a forgery, including
   the case where the protocol only sees a signature on a commitment body;
5. a forking or unique-signature argument if the bad event is equivocation
   rather than forgery;
6. a bound on the number of signing queries, plus the standard-model or
   generic-group justification for the `q_s/2^λ` shape;
7. a treatment of nonce generation and signature malleability, or an explicit
   assumption that the implementation is canonical.

None of these is proved in the tree.

---

## 6. C8: HMAC PRF and binding limits

### 6.1 What the standard assumptions say

There are three different statements that are often conflated:

| Statement | Meaning | Relation to C8 |
|---|---|---|
| PRF security | `HMAC(k, ·)` is indistinguishable from a random function | not modelled |
| MAC/EUF-CMA | no forgery of a tag on an unqueried message | not modelled |
| Tag binding | equal tags on a finite message list imply equal messages | `HmacBindsOn` |

HMAC-SHA256 has a 32-byte tag. The Bellare–Canetti–Krawczyk analysis and
Bellare's later proof give PRF bounds under assumptions on the compression
function. The unordered-pair collision probability for `q` tags is about
`(q(q-1)/2)/2^256 ≈ q²/2^257`; a conservative reduction charge is
`q²/2^256`. A forgery term is about `q_v/2^256`.

### 6.2 What the Lean model gives

`HmacBindsOn` is a finite-execution tag-binding admission. The exact algebraic
fact added by this lane is:

```lean
def HmacTagCollisionOn (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) : Prop :=
  ∃ m₁ ∈ msgs, ∃ m₂ ∈ msgs, m₁ ≠ m₂ ∧ M.hmacSha256 mu m₁ = M.hmacSha256 mu m₂

theorem algebraic_c8_no_tag_collision (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (h : HmacBindsOn M.hmacSha256 mu msgs) :
    ¬ HmacTagCollisionOn M mu msgs
```

This is a consequence of the finite admission. It is not a PRF statement.

### 6.3 Why the exact binding assumption is not a PRF reduction

A PRF adversary is allowed to see tags on many messages. A collision among
those tags is an expected event with probability about `q²/2^256`; it is not a
PRF break. Therefore:

* `HmacBindsOn` (no collision at all on the execution's finite list) requires
  exact collision-freedom; PRF security does not imply it;
* a protocol proof that consumes `HmacBindsOn` must either assume exact
  collision-freedom (a non-standard, non-computational assumption) or add a
  game hop that aborts on a tag collision and charges `q²/2^256`;
* a tag collision on two *queried* messages is not a MAC forgery; only a tag
  on an *unqueried* message is. The extraction argument must distinguish these
  cases.

This is the central C8 gap and the reason `docs/HMAC-LIMITS.md` says that
computational HMAC security is outside the model.

### 6.4 What a C8 reduction would need

1. a PRF game for `HMAC(k, ·)` and a MAC/EUF-CMA game with a verification
   oracle;
2. a key schedule and domain-separation model for the Sphinx `mu` values,
   including what happens across onion layers and sessions;
3. a game hop that replaces HMAC by a random function, with a bound on the
   distinguishing advantage;
4. a collision-abort hop for the finite message list, with the birthday term;
5. a proof that the protocol's authentication failure yields either a tag
   collision or a forgery on an unqueried message;
6. a treatment of associated data and concatenation ambiguity (the model uses
   `hop_payloads ++ associated_data`; real BOLT 4 uses a structured packet);
7. a bound on the number of onion layers/queries and the tag length.

The finite `HmacBindsOn` admission is a useful specification of the local
binding property, but it is not a substitute for this reduction.

---

## 7. The algebraic-versus-computational gap

The gap is not a single missing lemma. It has several independent dimensions.

### 7.1 Exact laws versus asymptotic bounds

`CollisionResistant` says "there is no collision". Computational collision
resistance says "no efficient adversary finds one with non-negligible
probability". The first implies the second for the abstract function in the
model, but the model's function is an arbitrary parameter, not SHA-256. The
second does not imply the first: a function can have collisions that are hard
to find. Consequently:

* the algebraic theorem `algebraic_c1_no_collision` is true for every
  `PrimitiveModel` satisfying C1, but it is not a statement about the deployed
  hash;
* replacing the computational assumption by the exact one is a strengthening
  that standard cryptography does not justify;
* the exact form is used because it makes the protocol proofs simple and
  keeps every assumption visible, not because it is a proved property of
  SHA-256.

Unlike the refuted global `HmacPrf`/`PreimageResistant` forms, C1 is
satisfiable together with `sha256_size`: the function that is the identity on
32-byte inputs and constant (e.g. all-zero) elsewhere is injective on the
32-byte domain and always returns 32 bytes. The model is therefore not
vacuous; it is an idealisation of the deployed hash.

### 7.2 Message binding is not unforgeability

`EufCma` is a uniqueness property of the verifier. A reject-all verifier
satisfies it. It is therefore not, by itself, a security assumption. The
protocol needs at least:

* `SigningCompleteness`: honestly produced signatures verify;
* `KeyBinding`: the verification key is the intended party's key;
* an unforgeability game: no accepted signature on a message the honest party
  did not sign.

C3 in `docs/ASSUMPTIONS.md` says "existential unforgeability under chosen
message", but the Lean field is only the message-binding consequence. This
naming gap must be kept in release wording.

### 7.3 Finite binding is not a PRF

`HmacBindsOn` is a finite-list uniqueness property. It is satisfiable by any
injective-on-that-list function, including a function with no cryptographic
strength. It does not say that tags are unpredictable, that keys are secret,
or that an adversary cannot forge. It is a local specification, not a
computational assumption.

### 7.4 Event security does not determine advantage

The Lean module makes this gap formal. The one-state game with no bad event is
event-secure:

```lean
def unitGame : Game where
  State := Unit
  init := ()
  step := fun s _ => s
  bad := fun _ => False

theorem unitGame_secure : unitGame.Secure
```

The same game admits both the zero advantage and the one advantage:

```lean
theorem event_game_does_not_determine_advantage :
    ∃ (A B : Advantage unitGame),
      (∀ n, A.value n = 0) ∧ (∀ n, B.value n = 1)
```

and a secure game can carry advantage arbitrarily close to one:

```lean
theorem secure_game_unbounded_advantage :
    unitGame.Secure ∧
      ∀ ε : Rat, ε < 1 → ∃ A : Advantage unitGame, ¬ A.value 0 ≤ ε
```

This is not a paradox; it is the statement that `Game` has no probability
semantics. The event-level theorem `EventReduction.secure` transfers "no bad
state", but it says nothing about the probability of a bad state under a
randomised adversary. A reduction cannot be replaced by the event-level
theorem.

### 7.5 What the exact model can and cannot express

| Ingredient | In the current tree | Needed for a computational claim |
|---|---|---|
| State transition | yes (`Game`, protocol transition functions) | yes, plus adversary-controlled scheduling |
| Bad event | yes (`Game.bad`) | yes |
| Probability | no | distribution over coins and oracle answers |
| Efficiency | no | PPT/runtime bound |
| Oracle access | no | signing, hash, HMAC, random-oracle games |
| Negligible | definition only | closure, composition, game hopping |
| Reduction | event-level only | adversary transformation, tightness, efficiency |
| Key generation | no | `KeyGen`, corruption model |
| Key binding | hypothesis (`KeyBinding`) | registration/proof-of-possession game |
| Signing correctness | hypothesis (`SigningCompleteness`) | `Sign`/`Verify` correctness theorem |
| Serialisation/sighash | partial | BOLT 3 byte-exact domain |
| L1/network | separate assumptions | integrated protocol game |

---

## 8. What a game-based reduction would need, precisely

This section states the theorem shape that a future computational development
would have to prove. It is a research plan, not a claim.

### 8.1 Games

Define at least:

```text
CR_H(A, λ)        collision game for SHA-256
PRE_H(A, λ)       preimage game for SHA-256
EUFCMA_ECDSA(A, λ) ECDSA unforgeability with a signing oracle
KEYBIND(A, λ)     key-registration / key-ownership game
PRF_HMAC(A, λ)    HMAC pseudorandomness
MAC_HMAC(A, λ)    HMAC unforgeability
G_PROTOCOL(A, λ)  the Lightning protocol game
```

`G_PROTOCOL` must fix:

* the corruption model (static or adaptive, which parties);
* the network schedule (asynchronous, delayed, partitioned);
* the L1 model (confirmation, reorg depth, timelocks);
* the honest-party behaviour (including watchtower or not);
* the winning condition (theft, value creation, equivocation, stuck funds,
  privacy, ...);
* the environment's ability to choose messages, keys, and channels.

The current wave-A `SecurityGame` and the phase-C3 finite game are useful
state-machine skeletons, but neither is a probabilistic protocol game.

### 8.2 Reduction record

A reduction `R` from `G_PROTOCOL` to a primitive game `G_C` must provide:

```text
R : Adversary_PROTOCOL → Adversary_C
```

plus:

1. **State map and event transport** — mechanised here as `EventReduction`:
   `map : P.State → C.State`, `map_init`, `map_step`,
   `win_transport : P.bad s → C.bad (map s)`.
2. **Advantage accounting** — mechanised here as the `tight` field of
   `AdvantageReduction`:
   `Adv_P(A, n) ≤ Adv_C(R(A), n) + loss(A, n)`.
3. **Loss negligibility** — not mechanised:
   `Negligible (fun n => loss(A, n))`.
4. **Efficiency preservation** — not mechanised:
   `time(R(A)) ≤ poly(time(A))`.
5. **Oracle simulation correctness** — not mechanised: the reduction's answers
   to `A`'s oracle queries must be distributed as in the real game, with the
   game-hop losses accounted for.
6. **Extraction** — not mechanised: a protocol bad event must yield a
   primitive-game win, not merely an algebraic contradiction.
7. **Composition** — not mechanised: if the protocol uses C1, C3, and C8, the
   losses must be summed and the sum proved negligible (the
   `CompositeAdvantage` record states the arithmetic shape).

### 8.3 The theorem that would follow

With a probability semantics and a negligible predicate closed under addition,
the target is:

```text
theorem protocol_secure
    (A : Adversary_PROTOCOL)
    (hC : Negligible (fun λ => Adv_C (R A) λ))
    (hloss : Negligible (fun λ => loss A λ)) :
    Negligible (fun λ => Adv_PROTOCOL A λ)
```

The Lean module proves only the arithmetic core:

```lean
theorem AdvantageReduction.bound
    (R : AdvantageReduction P C) {ε : Nat → Rat}
    (h : ∀ n, R.primitive.value n ≤ ε n) :
    ∀ n, R.protocol.value n ≤ ε n + R.loss n

theorem AdvantageReduction.bound_of_ideal
    (R : AdvantageReduction P C) {δ : Nat → Rat}
    (hzero : ∀ n, R.primitive.value n = 0)
    (hδ : ∀ n, R.loss n ≤ δ n) :
    ∀ n, R.protocol.value n ≤ δ n
```

and the three-primitive union-bound shape:

```lean
theorem composite_bound (R : CompositeAdvantage) {b1 b3 b8 δ : Rat}
    (h1 : R.c1 ≤ b1) (h3 : R.c3 ≤ b3) (h8 : R.c8 ≤ b8)
    (hδ : R.loss ≤ δ) :
    R.protocol ≤ (b1 + b3 + b8) + δ
```

These are conditional arithmetic. They do not assert that a reduction exists.
Conversely, the interface is trivially satisfiable by choosing a large enough
`loss`; it is an accounting device, not evidence that a reduction exists. The
content of a real reduction is in proving `tight` with a *negligible* loss and
an efficient adversary transformation, neither of which is in this module.

### 8.4 Primitive-specific extraction obligations

| Primitive | Bad protocol event | Needed extraction | Main obstruction |
|---|---|---|---|
| C1 | same payment hash, two accepted preimages | output a 32-byte collision | preimages may be hidden; 32-byte domain ≠ script domain (`L1-05`) |
| C1 | same hash used in a 71-byte script | output a script collision | C1 does not cover scripts |
| C3 | accepted signature on an unsigned commitment | output an EUF-CMA forgery | sighash domain not modelled (`PR-02`); signing completeness missing |
| C3 | same signature on two commitment bodies | output a message-binding break | ECDSA is malleable; not a direct EUF-CMA win |
| C3 | signature attributed to the wrong party | win the key-binding game | `KeyBinding` is a separate hypothesis (`PR-01`) |
| C8 | tag accepted for a different payload | output a MAC forgery | tag may be on a queried message; binding is stronger than PRF |
| C8 | two payloads with the same tag | output a collision | PRF security permits collisions with negligible probability |

---

## 9. Exact Lean interface

File: `LnLean/Proofs/Security/SecurityGameTargets.lean`.
Namespace: `LnLean.Proofs.Security.Limits`.
Imports: `LnLean.Proofs.CryptoTargets`.

### 9.1 Games

```lean
structure Game where
  State : Type
  init : State
  step : State → Nat → State
  bad : State → Prop

def Game.run (g : Game) : Nat → g.State
def Game.Wins (g : Game) (n : Nat) : Prop
def Game.Secure (g : Game) : Prop
```

### 9.2 Event-level reduction

```lean
structure EventReduction (P C : Game) where
  map : P.State → C.State
  map_init : map P.init = C.init
  map_step : ∀ (s : P.State) (n : Nat), map (P.step s n) = C.step (map s) n
  win_transport : ∀ s : P.State, P.bad s → C.bad (map s)

theorem EventReduction.map_run (R : EventReduction P C) :
    ∀ n : Nat, R.map (P.run n) = C.run n

theorem EventReduction.secure (R : EventReduction P C) (hC : C.Secure) :
    P.Secure

def identityReduction (g : Game) : EventReduction g g
```

### 9.3 Advantage and the missing accounting inequality

```lean
structure Advantage (g : Game) where
  value : Nat → Rat
  nonneg : ∀ n : Nat, 0 ≤ value n
  le_one : ∀ n : Nat, value n ≤ 1

structure ExactAdvantage (g : Game) extends Advantage g where
  zero_of_secure : g.Secure → ∀ n : Nat, value n = 0

structure AdvantageReduction (P C : Game) where
  event : EventReduction P C
  protocol : Advantage P
  primitive : Advantage C
  loss : Nat → Rat
  loss_nonneg : ∀ n : Nat, 0 ≤ loss n
  tight : ∀ n : Nat, protocol.value n ≤ primitive.value n + loss n

theorem AdvantageReduction.bound (R : AdvantageReduction P C) {ε : Nat → Rat}
    (h : ∀ n : Nat, R.primitive.value n ≤ ε n) :
    ∀ n : Nat, R.protocol.value n ≤ ε n + R.loss n

theorem AdvantageReduction.bound_of_ideal (R : AdvantageReduction P C)
    {δ : Nat → Rat}
    (hzero : ∀ n : Nat, R.primitive.value n = 0)
    (hδ : ∀ n : Nat, R.loss n ≤ δ n) :
    ∀ n : Nat, R.protocol.value n ≤ δ n

structure CompositeAdvantage where
  protocol : Rat
  c1 : Rat
  c3 : Rat
  c8 : Rat
  loss : Rat
  loss_nonneg : 0 ≤ loss
  tight : protocol ≤ c1 + c3 + c8 + loss

theorem composite_bound (R : CompositeAdvantage) {b1 b3 b8 δ : Rat}
    (h1 : R.c1 ≤ b1) (h3 : R.c3 ≤ b3) (h8 : R.c8 ≤ b8)
    (hδ : R.loss ≤ δ) :
    R.protocol ≤ (b1 + b3 + b8) + δ
```

### 9.4 Cost model and assumed bounds

```lean
structure CostModel where
  securityParameter : Nat
  hashQueries : Nat
  signatureQueries : Nat
  hmacQueries : Nat

def c1CollisionBound (c : CostModel) : Rat
def c1PreimageBound (c : CostModel) : Rat
def c3EufCmaBound (c : CostModel) : Rat
def c8PrfBound (c : CostModel) : Rat

inductive Primitive
  | c1Collision
  | c1Preimage
  | c3EufCma
  | c8Prf

structure AssumedBound where
  primitive : Primitive
  cost : CostModel
  advantage : Rat
  bound : Rat
  assumed : advantage ≤ bound

def c1CollisionAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1CollisionBound c) : AssumedBound
def c1PreimageAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c1PreimageBound c) : AssumedBound
def c3EufCmaAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c3EufCmaBound c) : AssumedBound
def c8PrfAssumption (c : CostModel) (adv : Rat)
    (h : adv ≤ c8PrfBound c) : AssumedBound

theorem assumedBound_holds (A : AssumedBound) : A.advantage ≤ A.bound
theorem no_assumedBound_of_violation {adv bound : Rat}
    (h : ¬ adv ≤ bound) :
    ¬ ∃ A : AssumedBound, A.advantage = adv ∧ A.bound = bound
```

### 9.5 Negligibility

```lean
def Negligible (eps : Nat → Rat) : Prop :=
  ∀ c : Nat, 0 < c → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n ≤ (1 : Rat) / (c : Rat)
```

### 9.6 Algebraic facts

```lean
def Sha256Collision (M : PrimitiveModel) : Prop
theorem algebraic_c1_no_collision (M : PrimitiveModel)
    (h : CollisionResistant M.sha256) : ¬ Sha256Collision M

def EcdsaBindingFailure (M : PrimitiveModel) : Prop
theorem algebraic_c3_no_binding_failure (M : PrimitiveModel)
    (h : EufCma M.ecdsaVerify) : ¬ EcdsaBindingFailure M

def HmacTagCollisionOn (M : PrimitiveModel) (mu : ByteArray)
    (msgs : List ByteArray) : Prop
theorem algebraic_c8_no_tag_collision (M : PrimitiveModel)
    {mu : ByteArray} {msgs : List ByteArray}
    (h : HmacBindsOn M.hmacSha256 mu msgs) :
    ¬ HmacTagCollisionOn M mu msgs
```

### 9.7 The gap and non-vacuity

```lean
def unitGame : Game
theorem unitGame_secure : unitGame.Secure

def constantAdvantage {g : Game} (q : Rat) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    Advantage g

theorem event_game_does_not_determine_advantage :
    ∃ (A B : Advantage unitGame),
      (∀ n : Nat, A.value n = 0) ∧ (∀ n : Nat, B.value n = 1)

theorem secure_game_unbounded_advantage :
    unitGame.Secure ∧
      ∀ ε : Rat, ε < 1 →
        ∃ A : Advantage unitGame, ¬ A.value 0 ≤ ε

def zeroExactAdvantage : ExactAdvantage unitGame
theorem constantOne_not_exact :
    ¬ ∃ S : ExactAdvantage unitGame, ∀ n : Nat, S.value n = 1

def zeroReduction : AdvantageReduction unitGame unitGame
theorem zeroReduction_bound (n : Nat) :
    zeroReduction.protocol.value n ≤ zeroReduction.loss n
```

---

## 10. Assumption ledger

| Id | Lean form | Computational form (not modelled) | Bound recorded | Status |
|---|---|---|---|---|
| C1 collision | `CollisionResistant M.sha256` on 32-byte inputs | collision resistance of SHA-256 on arbitrary messages | `c1CollisionBound = q²/2^λ` | exact algebraic, conditional |
| C1 preimage | derived from `CollisionResistant` via `preimage_unique` | preimage/second-preimage resistance | `c1PreimageBound = q/2^λ` | not a separate Lean field |
| C3 | `EufCma M.ecdsaVerify` (message binding) | EUF-CMA with signing oracle | `c3EufCmaBound = q_s/2^λ` | exact algebraic, conditional; key binding and signing completeness separate |
| C8 | `HmacBindsOn M.hmacSha256 mu msgs` | PRF/MAC security | `c8PrfBound = q/2^λ` | finite algebraic; PRF not modelled |
| reduction | `EventReduction` + `AdvantageReduction.tight` | PPT reduction with negligible loss | `loss` | interface only; no reduction proved |

The ledger is intentionally not a claim that the computational forms are
true. It records which statement each Lean field is standing in for.

---

## 11. Scope caveats for any release text

Use the following wording:

* "The model is a conditionally safe model of Lightning's state machine under
  explicitly listed cryptographic and L1 assumptions."
* "C1, C3, and C8 are exact algebraic predicates, not computational-security
  proofs."
* "No reduction from a protocol attack to a primitive attack is mechanised."
* "The Lean development contains no probability space and no complexity
  model."

Do **not** write:

* "SHA-256 is collision resistant" (the field is assumed, and the model's
  domain is 32 bytes);
* "ECDSA is EUF-CMA" (the field is message binding, and a reject-all verifier
  satisfies it);
* "HMAC is a PRF" (the field is finite-execution binding, and global
  injectivity is false);
* "Lightning is computationally secure";
* "the reduction is proved".

The defensible release claim is the one already used by the tree: catalog rows
are model-level, conditional on C1-C8 and the L1/network assumptions in
`docs/ASSUMPTIONS.md`.

---

## 12. Recommended `docs/OPEN-ISSUES.md` wording

This lane does not edit `docs/OPEN-ISSUES.md`. The parent may replace the
`CR-01` and `SEC-01` rows with the following text.

### `CR-01`

> **Open.** C1/C3/C8 are exact algebraic laws, not computational reductions.
> `LnLean/Proofs/Security/SecurityGameTargets.lean` now records the missing
> interface: a finite game/event-reduction record, an `Advantage` /
> `AdvantageReduction` record whose `tight` field is the reduction accounting
> inequality, conventional `q²/2^λ` and `q/2^λ` bounds for C1/C3/C8, and
> proofs of only the algebraic consequences (no 32-byte SHA-256 collision, no
> ECDSA message-binding failure, no finite-execution HMAC tag collision).
> `docs/CRYPTO-LIMITS.md` states the gap and the exact theorem a reduction
> would need. No probability space, PPT model, negligible-loss closure, or
> reduction is mechanised. **Next action:** a separate computational-security
> development, starting with a probability monad and the C1/C3/C8 games, not a
> rewording of the current fields.

### `SEC-01`

> **Open.** There is still no end-to-end game-based security proof for the
> protocol. The wave-5 limits module defines the game and advantage interface
> and proves that the event-level game does not determine an advantage
> (`event_game_does_not_determine_advantage`,
> `secure_game_unbounded_advantage`), so an event-level safety theorem cannot
> be presented as a computational result. The reduction target is stated, not
> proved. **Next action:** fix the protocol game (corruption, schedule, L1,
> winning condition), the primitive games, and an adversary transformation;
> then prove `Adv_P ≤ Adv_C + loss` with a negligible loss. Keep this issue
> separate from catalog cleanup.

---

## 13. Human and research decisions

These are not agent decisions and are not made by this lane.

1. **Probability and complexity foundation.** Choose between a minimal
   finite-probability monad over `Rat`, mathlib's `PMF`/measure theory, or a
   paper-only computational development. This determines whether the
   `Advantage` interface can ever be connected to `Game.Wins`.
2. **Security parameter and bound shapes.** Fix `λ`, the query model, and
   whether the bounds are `q²/2^λ`, `q(q-1)/2^λ`, or concrete constants.
   Decide whether to model quantum adversaries.
3. **C1 assumption.** Decide whether the long-term model keeps exact
   32-byte injectivity (simple, stronger than standard) or moves to an
   asymptotic collision game (faithful, much more work). Record the answer in
   `docs/ASSUMPTIONS.md`; do not silently change the field.
4. **C3 assumption.** Decide whether to add `Sign`/`KeyGen` and
   `SigningCompleteness`, a `KeyBinding` game, and a real EUF-CMA game. Without
   these, "C3" is message binding and can be satisfied by a reject-all
   verifier.
5. **C8 assumption.** Decide between PRF, MAC/EUF-CMA, and finite tag binding.
   The current `HmacBindsOn` is not implied by PRF security; a reduction that
   uses it must add a collision-abort hop.
6. **Protocol game.** Fix the corruption model, schedule, L1 model, winning
   condition, and whether the claim is game-based or UC-style. The current
   finite games are not a protocol game.
7. **Sighash/serialisation.** Decide whether to mechanise BOLT 3 sighash and
   the exact byte domains (`PR-02`) before claiming a C3 reduction. Without
   it, the signed message is an abstract byte string.
8. **Key binding.** Decide whether `funding_pubkey` is bound by registration,
   proof of possession, or an authenticated handshake (`PR-01`).
9. **Effort and publication.** Decide whether to attempt a full mechanised
   reduction (large research project) or publish the current model with the
   limits document and a paper proof sketch. The latter is honest; the former
   is the only route to a computational claim.
10. **Wording.** Adopt the release wording in §11 and update the README /
    roadmap only after the decision.

---

## 14. References

* NIST FIPS 180-4, *Secure Hash Standard* (SHA-256).
* SEC 1, *Elliptic Curve Cryptography* (ECDSA encoding and verification).
* BIP 340, *Schnorr Signatures for secp256k1* (future taproot channels; C4).
* BOLT 1, *Base Protocol* (32-byte hashes and signatures).
* BOLT 2, *Peer Protocol* (funding, commitment, and closing signatures).
* BOLT 3, *Commitment Transactions* (sighash and output scripts).
* BOLT 4, *Onion Routing* (HMAC tags and the Sphinx packet).
* M. Bellare, R. Canetti, H. Krawczyk, "Keying Hash Functions for Message
  Authentication" (HMAC PRF analysis).
* M. Bellare, "New Proofs for NMAC and HMAC: Security without
  Collision-Resistance".
* D. Pointcheval, J. Stern, "Security Arguments for Digital Signatures and
  Blind Signatures" (forking lemma; generic-group signature arguments).
* D. Brown, "Generic Groups, Collision Resistance, and ECDSA".
* V. Shoup, "Lower Bounds for Discrete Logarithms and Related Problems"
  (generic-group model).
* `docs/HMAC-LIMITS.md` (the C8 boundary in this tree).
* `docs/ASSUMPTIONS.md` §1 (C1-C8 and the TCB).
* `LnLean/Proofs/CryptoTargets.lean` (the C1/C3/C8 algebraic contracts).
* `LnLean/Proofs/WaveE/E06.lean` (`SigningCompleteness`, `KeyBinding`).
