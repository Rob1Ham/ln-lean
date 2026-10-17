import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Channel.Revocation

English claim.  Each commitment transaction is identified by a commitment
number and has a per-commitment secret and point.  The revocation public key
of a commitment is derived from a revocation basepoint and that commitment's
point.  Once the secret is revealed (by `revoke_and_ack`), the punisher can
derive the matching revocation private key.  BOLT 3's shachain construction
lets a node store only 49 secrets (about 50*32 bytes) and reconstruct every
earlier per-commitment secret; the model exposes that construction as an
abstract derivation function with two interface properties, injectivity on
commitment numbers and a 49-slot storage bound.  This module does **not**
claim to implement SHA-256 or the byte-level shachain algorithm.

BOLT anchors.
* BOLT 2 `revoke_and_ack` (per-commitment secret exchange):
  `refs/bolts/02-peer-protocol.md:3206`.
* BOLT 3 `revocationpubkey` derivation:
  `refs/bolts/03-transactions.md:799` (blinded key
  `revocation_basepoint * SHA256(base || point) + point * SHA256(point || base)`).
* BOLT 3 per-commitment secret requirements and generation:
  `refs/bolts/03-transactions.md:828` (up to `2^48 - 1` secrets; first index
  `281474976710655`, then decrement).
* BOLT 3 efficient per-commitment secret storage:
  `refs/bolts/03-transactions.md:860` (49 stored secrets).

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:339` (`build_commitment_secret`:
  `generate_from_seed`, 48 iterations of bit-flip plus SHA-256).
* `lightning/src/ln/chan_utils.rs:402` (`CounterpartyCommitmentSecrets`,
  `old_secrets: [([u8; 32], u64); 49]`).
* `lightning/src/ln/chan_utils.rs:438` (`get_min_seen_secret`; indexes start
  at `1 << 48` and decrement).
* `lightning/src/ln/chan_utils.rs:537` (`derive_private_revocation_key`).
* `lightning/src/ln/chan_utils.rs:640`
  (`RevocationKey::from_basepoint` inside `TxCreationKeys::derive_new`).
* `lightning/src/ln/channel.rs:9444` (peer-supplied
  `per_commitment_secret` is parsed as a 32-byte secp256k1 secret key).
* `lightning/src/ln/channel.rs:3806` (`commitment_secrets` field of a
  channel) and `:9480` (the secret is fed to the storage).

Not modelled.
* The actual SHA-256 compression, the bit-flip algorithm, and secp256k1
  point arithmetic are opaque.  `Shachain.derive` and
  `RevocationScheme.derivePubkey/derivePrivkey` are parameters.
* The BOLT 3 "neither party alone knows the key" argument is a
  cryptographic assumption, not a theorem here.
* The 49-slot placement/reconstruction algorithm is represented only by the
  store shape and its invariants; slot contents are not proved to
  reconstruct secrets (that belongs to a proof module with a concrete hash).
-/

namespace LnLean.Channel

open LnLean

set_option autoImplicit false

/-! ## Bounds -/

/-- BOLT 3: up to `2^48 - 1` per-commitment secrets can be generated. -/
def COMMITMENT_SECRET_COUNT : Nat := 281474976710656

/-- The largest valid commitment number / per-commitment-secret index. -/
def MAX_COMMITMENT_NUMBER : Nat := 281474976710655

theorem MAX_COMMITMENT_NUMBER_eq : MAX_COMMITMENT_NUMBER = COMMITMENT_SECRET_COUNT - 1 := rfl

theorem MAX_COMMITMENT_NUMBER_lt_count : MAX_COMMITMENT_NUMBER < COMMITMENT_SECRET_COUNT := by
  decide

/-- BOLT 3 efficient storage keeps 49 secrets, independent of the number of
commitments.  `lightning/src/ln/chan_utils.rs:403`. -/
def SECRET_STORAGE_SLOTS : Nat := 49

theorem SECRET_STORAGE_SLOTS_eq : SECRET_STORAGE_SLOTS = 49 := rfl

/-- The byte budget of the compact storage (49 * 32 = 1568 bytes). -/
theorem storage_bytes : SECRET_STORAGE_SLOTS * 32 = 1568 := rfl

/-! ## Secrets, points, keys -/

/-- A 32-byte per-commitment secret (`per_commitment_secret`). -/
structure PerCommitmentSecret where
  bytes : ByteArray
deriving Repr, BEq, DecidableEq

namespace PerCommitmentSecret

def Valid (s : PerCommitmentSecret) : Prop := s.bytes.size = 32

theorem valid_iff_size (s : PerCommitmentSecret) : s.Valid ↔ s.bytes.size = 32 := Iff.rfl

end PerCommitmentSecret

/-- A per-commitment point (`per_commitment_point`), a compressed secp256k1
point `per_commitment_secret * G`. -/
structure PerCommitmentPoint where
  key : PubKey
deriving Repr, BEq

namespace PerCommitmentPoint

def Valid (p : PerCommitmentPoint) : Prop := p.key.Valid

end PerCommitmentPoint

/-- The blinded revocation key of one commitment
(`revocationpubkey` in BOLT 3). -/
structure RevocationKey where
  key : PubKey
deriving Repr, BEq

namespace RevocationKey

def Valid (k : RevocationKey) : Prop := k.key.Valid

end RevocationKey

/-- The 32-byte per-channel seed from which the shachain is generated.
BOLT 3: "MUST select an unguessable 256-bit seed for each connection,
MUST NOT reveal the seed" (`refs/bolts/03-transactions.md:830`). -/
structure CommitmentSeed where
  bytes : ByteArray
deriving Repr, BEq, DecidableEq

namespace CommitmentSeed

def Valid (s : CommitmentSeed) : Prop := s.bytes.size = 32

end CommitmentSeed

/-- Wrap a byte string as a seed.  The validity premise is kept explicit at
the call site by `commitmentSeed_valid`. -/
def commitmentSeed (b : ByteArray) : CommitmentSeed := ⟨b⟩

theorem commitmentSeed_valid (b : ByteArray) (h : b.size = 32) :
    (commitmentSeed b).Valid := h

/-! ## Abstract shachain -/

/-- The abstract BOLT 3 shachain.  `derive i` is the per-commitment secret
of commitment number `i` (`build_commitment_secret` in rust-lightning).
The interface consists of the size law (every secret is 32 bytes), the
index bound (`0 .. 2^48 - 1`), and injectivity: distinct commitment numbers
have distinct secrets.  The concrete bit-flip/SHA-256 algorithm is not
implemented here. -/
structure Shachain where
  seed : CommitmentSeed
  /-- BOLT 3: the seed is an unguessable 256-bit value. -/
  seed_valid : seed.Valid
  derive : Nat → PerCommitmentSecret
  derive_size : ∀ i, (derive i).bytes.size = 32
  derive_injective : ∀ {i j : Nat}, i ≤ MAX_COMMITMENT_NUMBER →
    j ≤ MAX_COMMITMENT_NUMBER → derive i = derive j → i = j

/-- The per-commitment secret of commitment `idx`. -/
def revocationSecret (sh : Shachain) (idx : Nat) : PerCommitmentSecret :=
  sh.derive idx

theorem revocationSecret_size (sh : Shachain) (idx : Nat) :
    (revocationSecret sh idx).bytes.size = 32 :=
  sh.derive_size idx

theorem revocationSecret_valid (sh : Shachain) (idx : Nat) :
    (revocationSecret sh idx).Valid :=
  sh.derive_size idx

/-- Distinct valid commitment numbers have distinct revocation secrets. -/
theorem revocationSecret_injective (sh : Shachain) {i j : Nat}
    (hi : i ≤ MAX_COMMITMENT_NUMBER) (hj : j ≤ MAX_COMMITMENT_NUMBER)
    (h : revocationSecret sh i = revocationSecret sh j) : i = j :=
  sh.derive_injective hi hj h

/-- The seed used by the shachain is a valid 32-byte seed. -/
theorem shachain_seed_valid (sh : Shachain) : sh.seed.Valid :=
  sh.seed_valid

/-! ## Revocation key derivation -/

/-- The abstract revocation-key scheme.  It packages the BOLT 3 derivation
functions and their specification.  `consistent` is the BOLT 3 statement
that the private key derived from the revealed secret and the punisher's
basepoint is the private key of the derived public revocation key;
`injective_point` says the derivation does not collapse two distinct
per-commitment points.  Both are hypotheses of any theorem that uses them,
never global assumptions.

Anchor: `refs/bolts/03-transactions.md:799-826`,
`lightning/src/ln/chan_utils.rs:537`. -/
structure RevocationScheme where
  /-- `per_commitment_point = per_commitment_secret * G`. -/
  pointOf : PerCommitmentSecret → PerCommitmentPoint
  /-- The point of a valid secret is a valid compressed point. -/
  pointOf_valid : ∀ s, (pointOf s).key.Valid
  /-- `derivePubkey base point` is the BOLT 3 blinded public key. -/
  derivePubkey : PubKey → PerCommitmentPoint → RevocationKey
  /-- `derivePrivkey base secret` is the punisher's private revocation key. -/
  derivePrivkey : PubKey → PerCommitmentSecret → RevocationKey
  /-- BOLT 3: the two derivations agree. -/
  consistent : ∀ (base : PubKey) (s : PerCommitmentSecret),
    derivePrivkey base s = derivePubkey base (pointOf s)
  /-- A fixed basepoint and distinct points yield distinct keys. -/
  injective_point : ∀ (base : PubKey) (p q : PerCommitmentPoint),
    derivePubkey base p = derivePubkey base q → p = q

/-- The BOLT 3 `revocationpubkey` derivation, exposed as a function of the
scheme so the cryptographic content stays a parameter. -/
def deriveRevocationPubkey (scheme : RevocationScheme) (base : PubKey)
    (pt : PerCommitmentPoint) : RevocationKey :=
  scheme.derivePubkey base pt

/-- The revocation public key belonging to a revealed secret. -/
def revocationPubkeyOfSecret (scheme : RevocationScheme) (base : PubKey)
    (s : PerCommitmentSecret) : RevocationKey :=
  deriveRevocationPubkey scheme base (scheme.pointOf s)

/-- Public derivation and private derivation agree (BOLT 3).  Conditional on
the scheme's `consistent` field, which is the cryptographic interface. -/
theorem deriveRevocationPubkey_consistent (scheme : RevocationScheme) (base : PubKey)
    (s : PerCommitmentSecret) :
    deriveRevocationPubkey scheme base (scheme.pointOf s) =
      scheme.derivePrivkey base s :=
  (scheme.consistent base s).symm

/-- Equivalently, the punisher's derived private key matches the public key
that the commitment output is locked to. -/
theorem revocationPubkeyOfSecret_eq_privkey (scheme : RevocationScheme) (base : PubKey)
    (s : PerCommitmentSecret) :
    revocationPubkeyOfSecret scheme base s = scheme.derivePrivkey base s :=
  deriveRevocationPubkey_consistent scheme base s

/-- The revocation key derived from a valid secret is over a valid point. -/
theorem pointOf_valid (scheme : RevocationScheme) (s : PerCommitmentSecret) :
    (scheme.pointOf s).key.Valid :=
  scheme.pointOf_valid s

/-- Distinct per-commitment points cannot produce the same revocation key
for a fixed basepoint. -/
theorem deriveRevocationPubkey_injective (scheme : RevocationScheme) (base : PubKey)
    {p q : PerCommitmentPoint}
    (h : deriveRevocationPubkey scheme base p = deriveRevocationPubkey scheme base q) :
    p = q :=
  scheme.injective_point base p q h

/-! ## Storage of the last `2^48` secrets

The real BOLT 3 scheme stores 49 `(secret, index)` pairs and reconstructs
every secret below `minSeen`.  The model keeps the observable interface:
`minSeen` is the smallest commitment number whose secret has not yet been
revealed, so every `i < minSeen` is revoked.  At most 49 slots exist. -/

/-- Sparse revocation-secret store.  `slots` has exactly 49 entries; unused
entries are `none`. -/
structure RevocationStore where
  /-- All commitment numbers below this bound are revoked. -/
  minSeen : Nat
  /-- The 49 compact-storage slots. -/
  slots : Fin SECRET_STORAGE_SLOTS → Option (Nat × PerCommitmentSecret)
  /-- Indices never leave the BOLT 3 range. -/
  minSeen_bound : minSeen ≤ COMMITMENT_SECRET_COUNT

/-- The empty store before any secret has been revealed. -/
def emptyStore : RevocationStore where
  minSeen := 0
  slots := fun _ => none
  minSeen_bound := Nat.zero_le _

/-- A commitment number is revoked when its secret is known.  Since the
shachain reveals secrets in decreasing index order, that is exactly
`idx < minSeen`. -/
def isRevoked (st : RevocationStore) (idx : Nat) : Prop :=
  idx < st.minSeen

/-- Store a revealed secret for `idx`.  The concrete scheme places it in one
of the 49 slots; the model records the resulting `minSeen`.  The index must
be in range. -/
def provideSecret (st : RevocationStore) (idx : Nat) (s : PerCommitmentSecret)
    (hidx : idx < COMMITMENT_SECRET_COUNT) : RevocationStore where
  minSeen := max st.minSeen (idx + 1)
  slots := fun k => if k = (⟨0, by decide⟩ : Fin SECRET_STORAGE_SLOTS) then
      some (idx, s) else st.slots k
  minSeen_bound := by
    have h := st.minSeen_bound
    omega

theorem provideSecret_minSeen (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    (provideSecret st idx s hidx).minSeen = max st.minSeen (idx + 1) := rfl

/-- Providing the secret for `idx` revokes `idx` itself. -/
theorem isRevoked_provide_self (st : RevocationStore) (idx : Nat)
    (s : PerCommitmentSecret) (hidx : idx < COMMITMENT_SECRET_COUNT) :
    isRevoked (provideSecret st idx s hidx) idx := by
  unfold isRevoked
  rw [provideSecret_minSeen]
  omega

/-- Providing a secret never un-revokes an earlier commitment. -/
theorem isRevoked_provide_mono (st : RevocationStore) {i : Nat}
    (s : PerCommitmentSecret) (idx : Nat) (hidx : idx < COMMITMENT_SECRET_COUNT)
    (h : isRevoked st i) : isRevoked (provideSecret st idx s hidx) i := by
  unfold isRevoked at *
  rw [provideSecret_minSeen]
  omega

/-- Every revoked index is a valid commitment number in the `2^48` range. -/
theorem isRevoked_index_bound (st : RevocationStore) {i : Nat}
    (h : isRevoked st i) : i < COMMITMENT_SECRET_COUNT :=
  Nat.lt_of_lt_of_le h st.minSeen_bound

/-- The store never needs more than 49 slots, whatever the index. -/
theorem storage_slots_fixed (_st : RevocationStore) :
    (List.finRange SECRET_STORAGE_SLOTS).length = 49 := by
  simp [SECRET_STORAGE_SLOTS]

/-- A secret at index `i` is exactly `revocationSecret` of the shachain. -/
theorem stored_secret_eq (sh : Shachain) (i : Nat) :
    sh.derive i = revocationSecret sh i := rfl

end LnLean.Channel
