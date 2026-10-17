import LnLean.Basic.Core
import LnLean.Bitcoin.Seam

/-!
# LnLean.Security.Model

English claim.  This module fixes the *shape* of the adversary and of the
security game used by every later Lightning safety/liveness statement.  It
does not assert that Lightning is secure: it gives a vocabulary in which a
protocol execution, an adversarial schedule, an on-chain reorganisation, a
fee spike, and the winning condition are explicit objects.  The eight
cryptographic assumptions of `docs/ASSUMPTIONS.md` are represented as data
(ids, primitive names, and an explicit `Prop` supplied by the caller), so no
assumption is ever silently introduced as an axiom.

BOLT sections.  BOLT 1 (message transport, adversarial delivery), BOLT 2
(channel updates and retransmission), BOLT 5 (on-chain fee/penalty
environment), BOLT 7 (gossip over an unreliable network).

`rust-lightning` anchors at commit `fe49009`:
* `lightning/src/ln/channelmanager.rs:17831` (`handle_channel_reestablish`,
  retransmission under an adversarial schedule);
* `lightning/src/ln/channelmanager.rs:10210` (`claim_funds`, the event an
  adversary tries to prevent);
* `lightning/src/ln/channel.rs:2378` and `:6648` (`force_shutdown`, the
  on-chain fallback);
* `lightning/src/chain/chaininterface.rs` (fee estimator interface used by
  the fee-spike capability).

What is NOT modelled.  This file has no concrete network, no cryptographic
implementation, no chain consensus, and no probabilistic polynomial-time
adversary.  The schedule is an abstract relation; corruption is a finite
set of node identifiers; reorgs are a depth budget; fee spikes are a
height-indexed feerate.  Computational security (negligible advantage) is
outside the Lean model; only the event-based winning predicate is formal.
-/

namespace LnLean.Security

set_option autoImplicit false

/-- A node is identified by a natural number in the abstract model.  The
wire-level `PubKey` identity is supplied by `LnLean.Crypto.Model` in wave B. -/
abbrev NodeId := Nat

/-- Adversarial network capability.  `delivery i j = true` means the
adversary may deliver message `i` to node `j`; a `false` entry means the
message is dropped or delayed beyond the horizon.  `partition` is symmetric
by convention, and `maxDelay` is the delay the adversary may choose before
stabilisation.  BOLT 1 §"Lightning Message Format"; BOLT 2
§"Message Retransmission". -/
structure NetworkSchedule where
  delivery : Nat → NodeId → Bool
  partition : NodeId → NodeId → Bool
  maxDelay : Nat
  reorders : Bool
  dropsMessages : Bool

/-- How much of a node the adversary controls.  `adaptive` means the
corruption decision may depend on messages observed so far (BOLT 2
`channel_reestablish` is the canonical recovery point). -/
inductive CorruptionMode where
  | none
  | passive
  | active
  | adaptive
deriving Repr, DecidableEq, BEq

/-- An on-chain reorganisation observed by the Lightning layer.  Only the
depth matters for the channel model; the actual block sequence belongs to
the L1 model (`Bitcoin.Data.*`, via `LnLean.Bitcoin.Seam`). -/
structure Reorg where
  fromHeight : Height
  depth : Nat
  newTip : ByteArray
deriving Repr

/-- Fee environment.  `base` is the BOLT 5 / BOLT 3 feerate; `atHeight`
lets the adversary raise fees after a party has broadcast a commitment
(`feeInsufficient` is then a precondition failure, not a safety failure). -/
structure FeeEnvironment where
  base : FeeRate
  atHeight : Height → FeeRate
  spikeAt : Option Height

/-- The full adversary record.  It bundles the four capabilities named in
the mission: scheduling, corruption, reorg, and fee manipulation.  The
fields are *capabilities*, not proofs that the adversary succeeds. -/
structure Adversary where
  schedule : NetworkSchedule
  corruption : CorruptionMode
  corrupted : List NodeId
  reorgDepth : Nat
  reorgBudget : Nat
  fees : FeeEnvironment
  learnsPreimages : Bool
  adaptive : Bool

/-- The nodes an adversary controls. -/
def Adversary.controls (a : Adversary) (n : NodeId) : Prop :=
  n ∈ a.corrupted

/-- A reorg is within the adversary's budget. -/
def Adversary.reorgAllowed (a : Adversary) (r : Reorg) : Prop :=
  r.depth ≤ a.reorgBudget

/-- Fee at a given height, as chosen by the adversary. -/
def Adversary.feeAt (a : Adversary) (h : Height) : FeeRate :=
  a.fees.atHeight h

/-- A chain view is the tip observed by the Lightning layer.  Safety
statements are relative to a common tip; deep-reorg behaviour is a separate
obligation (`LN-L1-003`). -/
structure ChainView where
  height : Height
  tip : ByteArray
  lastReorg : Option Reorg
deriving Repr

/-- A finite execution of a protocol under a fixed adversary.  `bad` is the
protocol-specific failure event (loss of funds, double spend, stuck HTLC,
...) and `honest` is the set of nodes the security claim protects. -/
structure SecurityGame (State : Type) where
  adversary : Adversary
  init : State
  step : State → Adversary → Nat → State
  bad : State → Prop
  honest : List NodeId

/-- The state after `n` adversarial steps.  This is a total function: the
modelling obligation is to make `step` total and to put all partiality in
`bad`/preconditions. -/
def SecurityGame.run {State : Type} (g : SecurityGame State) : Nat → State
  | 0 => g.init
  | n + 1 => g.step (g.run n) g.adversary n

/-- The adversary wins at step `n` if the protocol reaches a bad state. -/
def AdversaryWins {State : Type} (g : SecurityGame State) (n : Nat) : Prop :=
  g.bad (g.run n)

/-- The protocol wins at step `n` if the bad event is not reached. -/
def Winning {State : Type} (g : SecurityGame State) (n : Nat) : Prop :=
  ¬ AdversaryWins g n

/-- A game is secure when the adversary never wins, for every finite
horizon.  Safety theorems in wave B are instances of this definition with
the appropriate `bad` predicate; liveness theorems additionally quantify
over fair schedules. -/
def Secure {State : Type} (g : SecurityGame State) : Prop :=
  ∀ n : Nat, Winning g n

/-- A named assumption from `docs/ASSUMPTIONS.md`.  `formalStatement` is a
`Prop`, never an axiom: the caller supplies it as a hypothesis, which keeps
the trust boundary visible in the type of every dependent theorem. -/
structure Assumption where
  id : String
  primitive : String
  assumedProperty : String
  formalStatement : Prop

/-- The eight cryptographic assumptions C1--C8, with their formal statements
left as parameters.  Wave B's `LnLean.Crypto.Model` instantiates these with
the concrete Props of the primitive interface; a theorem that needs C1 takes
`ha : a.sha256CollisionResistant` explicitly. -/
structure CryptoAssumptions where
  sha256CollisionResistant : Prop
  hash160CollisionResistant : Prop
  ecdsaEufCma : Prop
  schnorrEufCma : Prop
  ecdhCdh : Prop
  hkdfPrf : Prop
  aeadCca : Prop
  hmacPrf : Prop

/-- C1: SHA-256 collision and preimage resistance. -/
def assumptionC1 (p : Prop) : Assumption :=
  { id := "C1", primitive := "SHA-256",
    assumedProperty := "collision resistance; preimage resistance",
    formalStatement := p }

/-- C2: HASH160 = RIPEMD160(SHA256(x)) collision resistance. -/
def assumptionC2 (p : Prop) : Assumption :=
  { id := "C2", primitive := "HASH160",
    assumedProperty := "collision resistance",
    formalStatement := p }

/-- C3: secp256k1 ECDSA existential unforgeability under chosen message. -/
def assumptionC3 (p : Prop) : Assumption :=
  { id := "C3", primitive := "secp256k1 ECDSA",
    assumedProperty := "EUF-CMA",
    formalStatement := p }

/-- C4: BIP 340 Schnorr existential unforgeability under chosen message. -/
def assumptionC4 (p : Prop) : Assumption :=
  { id := "C4", primitive := "BIP 340 Schnorr",
    assumedProperty := "EUF-CMA",
    formalStatement := p }

/-- C5: ECDH on secp256k1 computational Diffie-Hellman. -/
def assumptionC5 (p : Prop) : Assumption :=
  { id := "C5", primitive := "secp256k1 ECDH",
    assumedProperty := "computational Diffie-Hellman",
    formalStatement := p }

/-- C6: HKDF-SHA256 pseudorandomness. -/
def assumptionC6 (p : Prop) : Assumption :=
  { id := "C6", primitive := "HKDF-SHA256",
    assumedProperty := "pseudorandomness",
    formalStatement := p }

/-- C7: ChaCha20-Poly1305 IND-CCA and integrity. -/
def assumptionC7 (p : Prop) : Assumption :=
  { id := "C7", primitive := "ChaCha20-Poly1305",
    assumedProperty := "IND-CCA; ciphertext integrity",
    formalStatement := p }

/-- C8: HMAC-SHA256 PRF / unforgeability (onion integrity, gossip auth). -/
def assumptionC8 (p : Prop) : Assumption :=
  { id := "C8", primitive := "HMAC-SHA256",
    assumedProperty := "PRF; unforgeability",
    formalStatement := p }

/-- The catalog of C1--C8, in the order used by `docs/ASSUMPTIONS.md`. -/
def CryptoAssumptions.toList (a : CryptoAssumptions) : List Assumption :=
  [ assumptionC1 a.sha256CollisionResistant
  , assumptionC2 a.hash160CollisionResistant
  , assumptionC3 a.ecdsaEufCma
  , assumptionC4 a.schnorrEufCma
  , assumptionC5 a.ecdhCdh
  , assumptionC6 a.hkdfPrf
  , assumptionC7 a.aeadCca
  , assumptionC8 a.hmacPrf ]

/-- Every assumption in the catalog has a non-empty id and primitive. -/
def Assumption.WellFormed (a : Assumption) : Prop :=
  a.id ≠ "" ∧ a.primitive ≠ ""

/-- The catalog is structurally well formed; this is a fact about the
representation, not about the truth of the assumptions. -/
theorem CryptoAssumptions.toList_wellFormed (a : CryptoAssumptions) :
    ∀ x : Assumption, x ∈ a.toList → x.WellFormed := by
  intro x hx
  simp [CryptoAssumptions.toList] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst x <;>
    simp [Assumption.WellFormed, assumptionC1, assumptionC2, assumptionC3,
      assumptionC4, assumptionC5, assumptionC6, assumptionC7, assumptionC8]

/-- At time zero the game is in its initial state. -/
@[simp] theorem SecurityGame.run_zero {State : Type} (g : SecurityGame State) :
    g.run 0 = g.init := rfl

/-- One unfolding of the run function. -/
theorem SecurityGame.run_succ {State : Type} (g : SecurityGame State) (n : Nat) :
    g.run (n + 1) = g.step (g.run n) g.adversary n := rfl

/-- Winning is exactly the negation of the bad event. -/
theorem winning_iff_not_bad {State : Type} (g : SecurityGame State) (n : Nat) :
    Winning g n ↔ ¬ g.bad (g.run n) :=
  Iff.rfl

/-- A secure game wins at every horizon. -/
theorem secure_implies_winning {State : Type} (g : SecurityGame State)
    (h : Secure g) (n : Nat) : Winning g n :=
  h n

/-- A game with no reachable bad state is secure. -/
theorem secure_of_no_bad {State : Type} (g : SecurityGame State)
    (h : ∀ n : Nat, ¬ g.bad (g.run n)) : Secure g :=
  h

/-- Corruption is monotone in the recorded set: a controlled node stays
controlled until the game says otherwise.  This is a bookkeeping lemma about
the record, not a protocol claim. -/
theorem controls_of_mem {a : Adversary} {n : NodeId} (h : n ∈ a.corrupted) :
    a.controls n :=
  h

end LnLean.Security
