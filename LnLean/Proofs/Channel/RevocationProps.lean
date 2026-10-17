import LnLean.Basic.Core
import LnLean.Channel.Revocation

/-!
# LnLean.Proofs.Channel.RevocationProps

English claim.  This module proves the structural part of the BOLT 3
per-commitment revocation scheme as exposed by `LnLean.Channel.Revocation`:

* a per-commitment secret is 32 bytes and its per-commitment point is a
  33-byte compressed secp256k1 point;
* the secret and the point of a fixed shachain instance are *definitionally*
  the model's derivation function applied to the commitment number;
* the BOLT 3 revocation-key derivation is a function of the per-commitment
  point and is injective on points; consequently it is injective on secrets
  whenever the scalar-to-point map is injective (the latter is a property of
  a concrete secp256k1 instantiation, not of the abstract interface);
* distinct commitment numbers in the `2^48` range have distinct secrets, so
  a secret is never reused;
* the sparse store revokes exactly the indices below `minSeen`, has at most
  `2^48` revoked indices and only 49 storage slots, and revealing the secret
  of an old commitment revokes that old commitment (and every older one) but
  not the current commitment.

Anchors (pinned commits in `refs/PINNED.md`).
* BOLT 2 `revoke_and_ack` and its 32-byte `per_commitment_secret`:
  `refs/bolts/02-peer-protocol.md:3206`, `refs/bolts/02-peer-protocol.md:3223`,
  `refs/bolts/02-peer-protocol.md:3229`.
* BOLT 3 per-commitment point and `revocationpubkey` derivation:
  `refs/bolts/03-transactions.md:799`, `refs/bolts/03-transactions.md:810`,
  `refs/bolts/03-transactions.md:817`, `refs/bolts/03-transactions.md:826`.
* BOLT 3 secret requirements (`2^48 - 1`, first index `281474976710655`) and
  the 49-slot compact storage: `refs/bolts/03-transactions.md:834`,
  `refs/bolts/03-transactions.md:837`, `refs/bolts/03-transactions.md:863`.
* rust-lightning `build_commitment_secret` (48 SHA-256 rounds):
  `lightning/src/ln/chan_utils.rs:339`.
* rust-lightning `CounterpartyCommitmentSecrets` and its
  `old_secrets: [([u8; 32], u64); 49]` storage:
  `lightning/src/ln/chan_utils.rs:402`, `lightning/src/ln/chan_utils.rs:403`,
  `lightning/src/ln/chan_utils.rs:423`, `lightning/src/ln/chan_utils.rs:439`,
  `lightning/src/ln/chan_utils.rs:465`.
* rust-lightning `derive_private_revocation_key`:
  `lightning/src/ln/chan_utils.rs:537`.
* rust-lightning `RevocationKey::from_basepoint`:
  `lightning/src/ln/chan_utils.rs:640`.
* rust-lightning parsing/checking a peer-supplied secret:
  `lightning/src/ln/channel.rs:9444`, `lightning/src/ln/channel.rs:9480`.

Not modelled.
* The concrete `generate_from_seed`/`derive_secret` bit-flip loop and
  SHA-256 compression are opaque: `Shachain.derive` is an interface field.
  In particular this file proves that a fixed `Shachain` instance determines
  its secrets and points as a function of the commitment number, but it does
  **not** prove that two different `Shachain` values with the same `seed`
  bytes have the same `derive`; that is a missing field of the wave-A
  interface, recorded in `agents/reports/B14.md`.
* secp256k1 scalar multiplication is opaque.  Injectivity of `pointOf` is a
  hypothesis of the secret-level injectivity theorem, not a global result.
* The 49-slot *placement and reconstruction* algorithm is not implemented;
  only the slot count and the `minSeen` abstraction are proved about.
* The "neither party alone knows the key" argument is a cryptographic
  assumption (BOLT 3 `03-transactions.md:820`), not a theorem here.
-/

namespace LnLean.Channel

open LnLean

set_option autoImplicit false

/-! ## Byte-level shapes -/

/-- A per-commitment secret produced by the shachain is exactly 32 bytes.
BOLT 3 `03-transactions.md:834`, LDK `chan_utils.rs:339`. -/
theorem secret_bytes_eq_32 (sh : Shachain) (i : Nat) :
    (revocationSecret sh i).bytes.size = 32 :=
  sh.derive_size i

/-- A per-commitment point is a valid compressed secp256k1 point, i.e. 33
bytes on the wire.  The mission brief's phrase "32 bytes" applies to the
*secret*; the point is a compressed curve point (BOLT 3
`03-transactions.md:810`, LDK `chan_utils.rs:640`). -/
theorem point_bytes_eq_33 (scheme : RevocationScheme) (s : PerCommitmentSecret) :
    (scheme.pointOf s).key.bytes.size = 33 := by
  simpa [PerCommitmentPoint.Valid, PubKey.Valid] using scheme.pointOf_valid s

/-- The per-channel shachain seed is 32 bytes (BOLT 3
`03-transactions.md:828`). -/
theorem seed_bytes_eq_32 (sh : Shachain) : sh.seed.bytes.size = 32 := by
  simpa [CommitmentSeed.Valid] using sh.seed_valid

/-- A secret obtained from `revocationSecret` is a valid model secret. -/
theorem revocationSecret_valid' (sh : Shachain) (i : Nat) :
    (revocationSecret sh i).Valid :=
  sh.derive_size i

/-! ## Definitional derivation from the commitment number -/

/-- The model's secret derivation is definitionally the shachain function
applied to the commitment number. -/
theorem revocationSecret_def (sh : Shachain) (i : Nat) :
    revocationSecret sh i = sh.derive i := rfl

/-- The public revocation key of a secret is definitionally the blinded key of
the corresponding per-commitment point. -/
theorem revocationPubkeyOfSecret_def (scheme : RevocationScheme) (base : PubKey)
    (s : PerCommitmentSecret) :
    revocationPubkeyOfSecret scheme base s =
      deriveRevocationPubkey scheme base (scheme.pointOf s) := rfl

/-- The same derivation is definitionally `scheme.derivePubkey`, the BOLT 3
`revocationpubkey` function. -/
theorem revocationPubkeyOfSecret_eq_pubkey (scheme : RevocationScheme) (base : PubKey)
    (s : PerCommitmentSecret) :
    revocationPubkeyOfSecret scheme base s =
      scheme.derivePubkey base (scheme.pointOf s) := rfl

/-- The point associated with commitment `i` is the model derivation composed
with `pointOf`; this is the sense in which the commitment number determines
the point. -/
theorem pointOf_revocationSecret_def (scheme : RevocationScheme) (sh : Shachain)
    (i : Nat) :
    scheme.pointOf (revocationSecret sh i) = scheme.pointOf (sh.derive i) := rfl

/-! ## Injectivity of the revocation-key derivation -/

/-- For a fixed basepoint, the BOLT 3 blinded-key map is injective on
per-commitment points.  This is the `injective_point` field of the model's
`RevocationScheme`, i.e. the stated crypto interface assumption. -/
theorem deriveRevocationPubkey_point_injective (scheme : RevocationScheme)
    (base : PubKey) :
    Function.Injective (fun p : PerCommitmentPoint =>
      deriveRevocationPubkey scheme base p) := by
  intro p q h
  exact scheme.injective_point base p q h

/-- If scalar-to-point is injective for a concrete scheme, then the public
revocation key is injective as a function of the secret.  The extra hypothesis
is exactly the secp256k1 group-law fact not present in the abstract
`RevocationScheme` interface. -/
theorem revocationPubkeyOfSecret_injective
    (scheme : RevocationScheme) (base : PubKey)
    (hpoint : Function.Injective scheme.pointOf) :
    Function.Injective (fun s : PerCommitmentSecret =>
      revocationPubkeyOfSecret scheme base s) := by
  intro s t h
  apply hpoint
  apply deriveRevocationPubkey_point_injective scheme base
  simpa [revocationPubkeyOfSecret] using h

/-- Distinct commitment numbers in the BOLT 3 range have distinct secrets.
This is the model's `derive_injective` interface property. -/
theorem distinct_commitments_distinct_secrets (sh : Shachain) {old current : Nat}
    (hne : old ≠ current)
    (hold : old ≤ MAX_COMMITMENT_NUMBER)
    (hcurrent : current ≤ MAX_COMMITMENT_NUMBER) :
    revocationSecret sh old ≠ revocationSecret sh current := by
  intro h
  exact hne (revocationSecret_injective sh hold hcurrent h)

/-- A concrete instance of the previous statement: the secrets at commitment
numbers `0` and `1` differ.  The bounds are discharged by `decide`. -/
theorem secrets_at_zero_and_one_differ (sh : Shachain) :
    revocationSecret sh 0 ≠ revocationSecret sh 1 := by
  apply distinct_commitments_distinct_secrets
  · decide
  · decide
  · decide

/-- No secret is reused between two different valid commitment numbers.  This
is the "never reuses one" half of the storage claim, stated directly over the
shachain rather than over the sparse store. -/
theorem no_secret_reuse (sh : Shachain) {i j : Nat}
    (hij : i ≠ j)
    (hi : i ≤ MAX_COMMITMENT_NUMBER)
    (hj : j ≤ MAX_COMMITMENT_NUMBER) :
    sh.derive i ≠ sh.derive j := by
  intro h
  exact hij (sh.derive_injective hi hj h)

/-! ## Arithmetic of the `2^48` bound -/

/-- BOLT 3 allows exactly `2^48` index values, of which `2^48 - 1` are valid
secret indices (the first index is `2^48 - 1`). -/
theorem commitment_secret_count_eq_two_pow_48 :
    COMMITMENT_SECRET_COUNT = 2 ^ 48 := by
  decide

/-- The largest commitment number is `2^48 - 1`. -/
theorem max_commitment_number_eq_two_pow_48_sub_one :
    MAX_COMMITMENT_NUMBER = 2 ^ 48 - 1 := by
  decide

/-! ## Sparse revocation store -/

/-- The store's revocation predicate is exactly membership in the range of
`minSeen`.  This is the checked structural characterisation of `isRevoked`. -/
theorem isRevoked_iff_mem_range (st : RevocationStore) (i : Nat) :
    isRevoked st i ↔ i ∈ List.range st.minSeen := by
  simp [isRevoked, List.mem_range]

/-- The logical set of revoked indices has at most `2^48` elements.  In the
model it is the initial segment `[0, minSeen)`, whose enumerating list has
length `minSeen`. -/
theorem revoked_count_le_two_pow_48 (st : RevocationStore) :
    (List.range st.minSeen).length ≤ COMMITMENT_SECRET_COUNT := by
  rw [List.length_range]
  exact st.minSeen_bound

/-- Every revoked commitment number lies below `2^48`. -/
theorem revoked_index_lt_two_pow_48 (st : RevocationStore) {i : Nat}
    (h : isRevoked st i) : i < 2 ^ 48 := by
  have hb := isRevoked_index_bound st h
  rwa [commitment_secret_count_eq_two_pow_48] at hb

/-- The compact storage has room for at most 49 `(secret, index)` pairs,
whatever the commitment history. -/
theorem storage_slots_le_49 (_st : RevocationStore) :
    (List.finRange SECRET_STORAGE_SLOTS).length ≤ 49 := by
  simp [SECRET_STORAGE_SLOTS]

/-- The empty store revokes no commitment. -/
theorem emptyStore_revokes_nothing (i : Nat) :
    ¬ isRevoked emptyStore i := by
  simp [isRevoked, emptyStore]

/-- Providing a secret never lowers `minSeen`; revocation is monotone in the
store. -/
theorem provideSecret_minSeen_mono (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    st.minSeen ≤ (provideSecret st idx s hidx).minSeen := by
  rw [provideSecret_minSeen]
  omega

/-- The exact post-state of `provideSecret`: an index is revoked iff it is
below `max st.minSeen (idx + 1)`. -/
theorem provideSecret_revoked_iff (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) (i : Nat) :
    isRevoked (provideSecret st idx s hidx) i ↔ i < max st.minSeen (idx + 1) := by
  unfold isRevoked
  rw [provideSecret_minSeen]

/-- If the store had not yet seen anything at or below `idx + 1`, then
revealing the secret of `idx` revokes exactly the commitments `0 .. idx`
(BOLT 3 descending shachain order). -/
theorem provideSecret_revokes_iff_le (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) (i : Nat)
    (hmin : st.minSeen ≤ idx + 1) :
    isRevoked (provideSecret st idx s hidx) i ↔ i ≤ idx := by
  rw [provideSecret_revoked_iff, Nat.max_eq_right hmin]
  omega

/-- Revealing the secret of the old commitment `idx` marks that old commitment
as revoked. -/
theorem old_revoked_by_revealed_secret (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    isRevoked (provideSecret st idx s hidx) idx :=
  isRevoked_provide_self st idx s hidx

/-- Revealing the secret of an old commitment does **not** revoke the next
(current) commitment.  This is the "not the current one" half of the claim,
under the explicit premise that the current commitment was not already
revoked before the update. -/
theorem next_not_revoked_by_old_secret (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT)
    (hmin : st.minSeen ≤ idx + 1) :
    ¬ isRevoked (provideSecret st idx s hidx) (idx + 1) := by
  rw [provideSecret_revoked_iff]
  omega

/-- A strictly newer commitment number is not revoked by revealing an old
secret, provided it is at least `minSeen` (so it was not already revoked). -/
theorem newer_not_revoked_by_old_secret (st : RevocationStore) (old current : Nat)
    (s : PerCommitmentSecret) (hidx : old < COMMITMENT_SECRET_COUNT)
    (hcurrent : st.minSeen ≤ current)
    (hlt : old < current) :
    ¬ isRevoked (provideSecret st old s hidx) current := by
  rw [provideSecret_revoked_iff]
  omega

/-- The model's `Shachain` interface is inhabited by any index-indexed secret
function that satisfies the size and injectivity fields.  This records that
the interface itself is consistent; it deliberately does not claim that the
BOLT 3 SHA-256 construction is such a function. -/
theorem exists_shachain_of_derivation (seed : CommitmentSeed) (hseed : seed.Valid)
    (derive : Nat → PerCommitmentSecret)
    (hsize : ∀ i, (derive i).bytes.size = 32)
    (hinj : ∀ {i j : Nat}, i ≤ MAX_COMMITMENT_NUMBER →
      j ≤ MAX_COMMITMENT_NUMBER → derive i = derive j → i = j) :
    ∃ sh : Shachain, sh.seed = seed ∧ ∀ i, sh.derive i = derive i := by
  exact ⟨⟨seed, hseed, derive, hsize, hinj⟩, rfl, fun _ => rfl⟩

end LnLean.Channel
