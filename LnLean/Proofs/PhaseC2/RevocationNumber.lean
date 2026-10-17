import LnLean.Basic.Core
import LnLean.Channel.Revocation
import LnLean.Proofs.Channel.RevocationProps

/-!
# LnLean.Proofs.PhaseC2.RevocationNumber

English claim.  In the BOLT 3 per-commitment revocation model of
`LnLean.Channel.Revocation`, a published per-commitment secret identifies at
most one commitment number in the valid range `0 .. MAX_COMMITMENT_NUMBER`.
The identification uses the shachain injectivity hypothesis already carried
by the model as `Shachain.derive_injective` (exposed for the derivation as
the theorem `revocationSecret_injective`): distinct valid commitment numbers
have distinct secrets, so a secret cannot belong to two numbers.

A published *per-commitment point* identifies at most one commitment number
only under an explicit injectivity hypothesis on `RevocationScheme.pointOf`,
the abstract secp256k1 scalar-to-point map.  The model's `RevocationScheme`
does not contain that field: it has `injective_point`, which is injectivity of
the BOLT 3 *blinded-key* map on points, not injectivity of the scalar map on
secrets.  The point and revocation-key uniqueness statements below therefore
take `Function.Injective scheme.pointOf` as a premise and are explicitly
conditional; they are not consequences of the stored injectivity field alone.

Finally, `RevocationStore.isRevoked` is downward closed in the commitment
number (a revoked `j` revokes every `i ≤ j`) and monotone in the stored index
`minSeen` (growing `minSeen` never un-revokes an index); `provideSecret` only
grows `minSeen`, hence it is monotone too.

BOLT anchors.
* BOLT 2 `revoke_and_ack` with the 32-byte `per_commitment_secret`:
  `refs/bolts/02-peer-protocol.md:3206`, `:3223`.
* BOLT 3 per-commitment point and `revocationpubkey` derivation:
  `refs/bolts/03-transactions.md:799`, `:810`, `:826`.
* BOLT 3 per-commitment secret generation and requirements
  (`2^48 - 1`, first index `281474976710655`):
  `refs/bolts/03-transactions.md:828`, `:834`, `:837`.
* BOLT 3 compact 49-slot secret storage: `refs/bolts/03-transactions.md:860`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:339` (`build_commitment_secret`).
* `lightning/src/ln/chan_utils.rs:402` (`CounterpartyCommitmentSecrets`,
  `old_secrets: [([u8; 32], u64); 49]`).
* `lightning/src/ln/chan_utils.rs:438` (`get_min_seen_secret`; the shachain
  walks indices downwards).
* `lightning/src/ln/chan_utils.rs:537` (`derive_private_revocation_key`).
* `lightning/src/ln/channel.rs:9444` (peer-supplied secret parsed as a
  32-byte secp256k1 scalar).

Not modelled.
* SHA-256, the shachain bit-flip loop, and secp256k1 scalar multiplication are
  opaque interfaces.  Injectivity of `Shachain.derive` is the model's
  hypothesis; injectivity of `RevocationScheme.pointOf` is an additional
  explicit hypothesis here, not a theorem of the abstract interface.
* The concrete 49-slot placement/reconstruction algorithm; only the
  `minSeen` abstraction of `RevocationStore` is reasoned about.
* The "neither party alone knows the revocation key" cryptographic argument.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Channel

set_option autoImplicit false

/-! ## Secret indices and commitment numbers -/

/-- `i` is a valid commitment number whose published per-commitment secret is
`s`.  The bound is `MAX_COMMITMENT_NUMBER`, the largest BOLT 3 index
(`2^48 - 1`). -/
def IsSecretIndex (sh : Shachain) (s : PerCommitmentSecret) (i : Nat) : Prop :=
  i ≤ MAX_COMMITMENT_NUMBER ∧ revocationSecret sh i = s

/-- The definition unfolded, for rewriting. -/
theorem isSecretIndex_iff (sh : Shachain) (s : PerCommitmentSecret) (i : Nat) :
    IsSecretIndex sh s i ↔
      i ≤ MAX_COMMITMENT_NUMBER ∧ revocationSecret sh i = s :=
  Iff.rfl

/-- Every valid commitment number indexes its own secret. -/
theorem isSecretIndex_self (sh : Shachain) {i : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) :
    IsSecretIndex sh (revocationSecret sh i) i :=
  ⟨hi, rfl⟩

/-- A published secret has **at most one** commitment number: two valid
numbers with the same secret are equal.  This is exactly the model's
`Shachain.derive_injective` hypothesis transported to `revocationSecret`. -/
theorem secretIndex_unique (sh : Shachain) {s : PerCommitmentSecret} {i j : Nat}
    (hi : IsSecretIndex sh s i) (hj : IsSecretIndex sh s j) : i = j := by
  rcases hi with ⟨hiBound, hiEq⟩
  rcases hj with ⟨hjBound, hjEq⟩
  exact revocationSecret_injective sh hiBound hjBound (hiEq.trans hjEq.symm)

/-- If a secret occurs at a valid commitment number, that number is unique. -/
theorem existsUnique_secretIndex (sh : Shachain) {s : PerCommitmentSecret}
    (h : ∃ i, IsSecretIndex sh s i) :
    ∃ i, IsSecretIndex sh s i ∧ ∀ j, IsSecretIndex sh s j → j = i := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, hi, fun j hj => secretIndex_unique sh hj hi⟩

/-- Direct form of the mission claim for secrets: equal published secrets at
valid indices imply equal commitment numbers. -/
theorem publishedSecret_identifies_commitment (sh : Shachain) {i j : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) (hj : j ≤ MAX_COMMITMENT_NUMBER)
    (h : revocationSecret sh i = revocationSecret sh j) : i = j :=
  revocationSecret_injective sh hi hj h

/-- Conversely, distinct valid commitment numbers publish distinct secrets:
no secret is reused across commitments. -/
theorem distinct_commitments_distinct_revocationSecrets (sh : Shachain) {i j : Nat}
    (hij : i ≠ j) (hi : i ≤ MAX_COMMITMENT_NUMBER)
    (hj : j ≤ MAX_COMMITMENT_NUMBER) :
    revocationSecret sh i ≠ revocationSecret sh j := by
  intro h
  exact hij (revocationSecret_injective sh hi hj h)

/-- A commitment whose secret is in the published image is identified by the
pair `(index, secret)` with the index in the BOLT 3 range. -/
theorem secretIndex_eq_of_published (sh : Shachain) {s : PerCommitmentSecret}
    {i j : Nat} (hi : IsSecretIndex sh s i) (hj : IsSecretIndex sh s j) :
    i = j :=
  secretIndex_unique sh hi hj

/-! ## Point indices (conditional on scalar-to-point injectivity) -/

/-- `i` is a valid commitment number whose per-commitment point is `p`. -/
def IsPointIndex (scheme : RevocationScheme) (sh : Shachain)
    (p : PerCommitmentPoint) (i : Nat) : Prop :=
  i ≤ MAX_COMMITMENT_NUMBER ∧ scheme.pointOf (revocationSecret sh i) = p

/-- The definition unfolded, for rewriting. -/
theorem isPointIndex_iff (scheme : RevocationScheme) (sh : Shachain)
    (p : PerCommitmentPoint) (i : Nat) :
    IsPointIndex scheme sh p i ↔
      i ≤ MAX_COMMITMENT_NUMBER ∧
        scheme.pointOf (revocationSecret sh i) = p :=
  Iff.rfl

/-- The point of a valid commitment number indexes that number. -/
theorem isPointIndex_self (scheme : RevocationScheme) (sh : Shachain) {i : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) :
    IsPointIndex scheme sh (scheme.pointOf (revocationSecret sh i)) i :=
  ⟨hi, rfl⟩

/-- A published per-commitment point identifies at most one commitment number,
**provided** the scalar-to-point map is injective.  This injectivity is the
explicit missing secp256k1 interface field; it is not implied by
`Shachain.derive_injective` or by `RevocationScheme.injective_point`. -/
theorem pointIndex_unique (scheme : RevocationScheme) (sh : Shachain)
    (hpoint : Function.Injective scheme.pointOf) {p : PerCommitmentPoint}
    {i j : Nat} (hi : IsPointIndex scheme sh p i)
    (hj : IsPointIndex scheme sh p j) : i = j := by
  rcases hi with ⟨hiBound, hiEq⟩
  rcases hj with ⟨hjBound, hjEq⟩
  apply revocationSecret_injective sh hiBound hjBound
  apply hpoint
  exact hiEq.trans hjEq.symm

/-- Direct form of the mission claim for points, under point injectivity. -/
theorem publishedPoint_identifies_commitment (scheme : RevocationScheme)
    (sh : Shachain) (hpoint : Function.Injective scheme.pointOf) {i j : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) (hj : j ≤ MAX_COMMITMENT_NUMBER)
    (h : scheme.pointOf (revocationSecret sh i) =
      scheme.pointOf (revocationSecret sh j)) : i = j := by
  apply revocationSecret_injective sh hi hj
  exact hpoint h

/-- If a point occurs at a valid commitment number, that number is unique,
under point injectivity. -/
theorem existsUnique_pointIndex (scheme : RevocationScheme) (sh : Shachain)
    (hpoint : Function.Injective scheme.pointOf) {p : PerCommitmentPoint}
    (h : ∃ i, IsPointIndex scheme sh p i) :
    ∃ i, IsPointIndex scheme sh p i ∧ ∀ j, IsPointIndex scheme sh p j → j = i := by
  rcases h with ⟨i, hi⟩
  exact ⟨i, hi, fun j hj => pointIndex_unique scheme sh hpoint hj hi⟩

/-- A published BOLT 3 revocation public key identifies at most one commitment
number, under point injectivity.  The proof chains
`revocationPubkeyOfSecret = derivePubkey ∘ pointOf`,
`deriveRevocationPubkey_injective` (the model's `injective_point` field), and
finally secret injectivity. -/
theorem revocationKey_identifies_commitment (scheme : RevocationScheme)
    (sh : Shachain) (base : PubKey) (hpoint : Function.Injective scheme.pointOf)
    {i j : Nat} (hi : i ≤ MAX_COMMITMENT_NUMBER)
    (hj : j ≤ MAX_COMMITMENT_NUMBER)
    (h : revocationPubkeyOfSecret scheme base (revocationSecret sh i) =
      revocationPubkeyOfSecret scheme base (revocationSecret sh j)) : i = j := by
  apply revocationSecret_injective sh hi hj
  apply hpoint
  apply deriveRevocationPubkey_injective scheme base
  simpa [revocationPubkeyOfSecret, deriveRevocationPubkey] using h

/-! ## Monotonicity of the revocation predicate -/

/-- `isRevoked` is definitionally the strict bound on the stored index. -/
theorem isRevoked_iff_lt_minSeen (st : RevocationStore) (i : Nat) :
    isRevoked st i ↔ i < st.minSeen :=
  Iff.rfl

/-- `isRevoked` is downward closed in the commitment number: if a commitment
is revoked, every older (smaller-numbered) one is revoked. -/
theorem isRevoked_mono (st : RevocationStore) {i j : Nat} (hij : i ≤ j)
    (hj : isRevoked st j) : isRevoked st i := by
  unfold isRevoked at *
  omega

/-- Monotonicity in the stored index: increasing `minSeen` only adds revoked
commitments, never removes them. -/
theorem isRevoked_mono_minSeen {st st' : RevocationStore}
    (h : st.minSeen ≤ st'.minSeen) {i : Nat} (hi : isRevoked st i) :
    isRevoked st' i := by
  unfold isRevoked at *
  omega

/-- Every revoked commitment number is a valid BOLT 3 commitment number, i.e.
at most `MAX_COMMITMENT_NUMBER`.  This bridges the store predicate to the
index range used by the secret/point identification theorems. -/
theorem revoked_index_le_max (st : RevocationStore) {i : Nat}
    (h : isRevoked st i) : i ≤ MAX_COMMITMENT_NUMBER := by
  have hb : i < COMMITMENT_SECRET_COUNT := isRevoked_index_bound st h
  have hc : MAX_COMMITMENT_NUMBER + 1 = COMMITMENT_SECRET_COUNT := rfl
  omega

/-- A revoked index is therefore a valid secret index. -/
theorem revoked_isSecretIndex (sh : Shachain) (st : RevocationStore) {i : Nat}
    (h : isRevoked st i) :
    IsSecretIndex sh (revocationSecret sh i) i :=
  isSecretIndex_self sh (revoked_index_le_max st h)

/-- `provideSecret` is monotone in the store order induced by `minSeen`, so it
never un-revokes an index. -/
theorem isRevoked_provideSecret_mono (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) {i : Nat}
    (h : isRevoked st i) : isRevoked (provideSecret st idx s hidx) i :=
  isRevoked_mono_minSeen (provideSecret_minSeen_mono st idx s hidx) h

/-- The stored index after revealing a secret is `max minSeen (idx + 1)`, so a
newly revealed old secret never lowers the revocation frontier. -/
theorem minSeen_le_provideSecret (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    st.minSeen ≤ (provideSecret st idx s hidx).minSeen :=
  provideSecret_minSeen_mono st idx s hidx

/-- When the frontier was not yet past `idx + 1`, revealing the secret of `idx`
revokes exactly the commitment numbers `0 .. idx` (the BOLT 3 descending
shachain order).  Bundled here to connect the store monotonicity with the
commitment-number range. -/
theorem provideSecret_revokes_range (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT)
    (hmin : st.minSeen ≤ idx + 1) {i : Nat} (hi : i ≤ idx) :
    isRevoked (provideSecret st idx s hidx) i := by
  rw [provideSecret_revokes_iff_le st idx s hidx i hmin]
  exact hi

/-- Every index revoked by a `provideSecret` step is a valid commitment
number, so the identification theorems apply to it. -/
theorem provideSecret_revoked_index_le_max (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) {i : Nat}
    (h : isRevoked (provideSecret st idx s hidx) i) : i ≤ MAX_COMMITMENT_NUMBER :=
  revoked_index_le_max (provideSecret st idx s hidx) h

end LnLean.Proofs.PhaseC2
