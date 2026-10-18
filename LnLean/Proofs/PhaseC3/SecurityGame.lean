import LnLean.Proofs.Common

/-!
# LnLean.Proofs.PhaseC3.SecurityGame

**English claim.**  This module formalises a small, finite safety game for a
Lightning channel and proves the adversary-level reduction requested by the
phase-C3 security lane: *if an adversary has a finite L1/network action
sequence that makes it win, then at least one explicit assumption has failed*.
A win is one of three events:

1. the ledger records more value than the channel's funding output
   (`CreatesValue`);
2. the adversary owns the contested output (`StealsContested`);
3. two finalised commitments equivocate: either the same signature verifies
   for two different commitment bodies, or the same payment hash is paired
   with two different preimages (`ConflictingFinals`).

The four assumptions are exactly the ones named in the mission:

* signature unforgeability (`Crypto.EufCma` over the game's verification
  function, assumption C3);
* hash binding (`HashBinding`: equal payment hashes imply equal preimages,
  assumption C1);
* L1 timelock enforcement (`TimelockEnforced`: an accepted claim at height
  `h` requires `expiry ≤ h`);
* channel conservation (`ChannelConserved`: every ledger transition accepted
  by the L1 bridge preserves `Ledger.Conserves`).

None of the four is an axiom.  They are `Prop`-valued fields of the
`Assumptions` structure.  The reduction theorem
`adversary_win_implies_assumption_failure` is a disjunction of their
negations, proved by case analysis over the finite action alphabet after an
inductive invariant.  There is also a bridge to the wave-A
`LnLean.Security.SecurityGame` record and a concrete parameter instance whose
four assumptions all hold, so the result is not vacuous.

BOLT sections.  BOLT 2 §"Adding an HTLC", §"Removing an HTLC",
§"Committing Updates So Far"; BOLT 3 §"Commitment Transaction",
§"HTLC-Timeout and HTLC-Success Transactions"; BOLT 5 §"Revoked Transaction
Close Handling"; BOLT 7 §"Recommendations for Routing".

`rust-lightning` anchors at commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:

* `lightning/src/ln/channel.rs:6270` (`build_commitment_transaction`) — the
  commitment whose finalisation is the `l1Finalize` action;
* `lightning/src/ln/channel.rs:9471` and
  `lightning/src/chain/channelmonitor.rs:5079` — revoked-commitment handling,
  the on-chain event that a conflicting final commitment would bypass;
* `lightning/src/ln/chan_utils.rs:1450` — commitment signature construction
  and verification (the `verify` parameter);
* `lightning/src/ln/chan_utils.rs:716` and `:841` — the commitment/HTLC
  value and script equations behind `Ledger.Conserves`;
* `lightning/src/chain/chaininterface.rs:350` — the fee/chain interface used
  by the L1 bridge.

What is **not** modelled.  There is no probability space, no concrete
SHA-256/secp256k1 implementation, no Bitcoin script interpreter, and no
mempool or package-relay model.  `GameParameters.acceptsLedger` and
`GameParameters.acceptsClaim` are abstract L1 acceptance oracles, and
`GameParameters.hash`/`verify` are abstract primitive interfaces.  The game
is deliberately finite: an action list, not an infinite strategy tree; the
bridge to `SecurityGame` therefore fixes a deterministic strategy
`Nat → GameState → Action`.  The contested output is a single Boolean owner,
not a full HTLC set, and commitment equivocation is the two concrete
collision shapes above, not all possible protocol deviations.
-/

namespace LnLean.Proofs.PhaseC3.SecurityGame

open LnLean
open LnLean.Security

set_option autoImplicit false

/-! ## 1. Primitive and L1 bridge parameters -/

/-- The cryptographic and L1 primitives used by the game.  Every field is a
plain function or data: the *properties* needed for safety are supplied
separately by `Assumptions`, never baked into this record. -/
structure GameParameters where
  /-- Commitment signature verification (C3 interface). -/
  verify : PubKey → ByteArray → EcdsaSig → Bool
  /-- Payment hash function (C1 interface). -/
  hash : Preimage → PaymentHash
  /-- L1 acceptance of a contested-output claim at a given height. -/
  acceptsClaim : Height → Height → Bool
  /-- L1 acceptance of a ledger transition. -/
  acceptsLedger : Ledger → Ledger → Bool
  /-- The honest party's public key. -/
  pk : PubKey
  /-- The honest party's opening balance, in millisatoshis. -/
  localFunding : Nat
  /-- The counterparty's opening balance, in millisatoshis. -/
  remoteFunding : Nat
  /-- The contested output's timelock expiry. -/
  expiry : Height

/-- The channel's funding value is fixed by the two opening balances. -/
def GameParameters.funding (P : GameParameters) : Nat :=
  P.localFunding + P.remoteFunding

/-- **Hash binding (C1).**  Equal payment hashes have equal preimages.  This
is the exact algebraic consequence of second-preimage resistance used by the
commitment-equivocation argument. -/
def HashBinding (P : GameParameters) : Prop :=
  ∀ p q : Preimage, P.hash p = P.hash q → p = q

/-- **L1 timelock enforcement.**  If the L1 bridge accepts a claim at height
`h` for an output expiring at `e`, then the timelock has elapsed. -/
def TimelockEnforced (P : GameParameters) : Prop :=
  ∀ h e : Height, P.acceptsClaim h e = true → e ≤ h

/-- **Channel conservation.**  Every ledger transition the L1 bridge accepts
preserves the conservation equation of `LnLean.Security.Ledger`.  This is the
bridge that rules out an accepted value-minting transition. -/
def ChannelConserved (P : GameParameters) : Prop :=
  ∀ l l' : Ledger, P.acceptsLedger l l' = true → l.Conserves → l'.Conserves

/-- The four assumption failures, one per explicit assumption. -/
def SignatureFailure (P : GameParameters) : Prop :=
  ¬ Crypto.EufCma P.verify

def HashFailure (P : GameParameters) : Prop :=
  ¬ HashBinding P

def TimelockFailure (P : GameParameters) : Prop :=
  ¬ TimelockEnforced P

def ChannelConservationFailure (P : GameParameters) : Prop :=
  ¬ ChannelConserved P

/-- **The reduction target.**  A winning strategy implies at least one of the
four named assumption failures.  This is the disjunction the mission asks
for; it is proved below, not introduced as an axiom. -/
def AssumptionFailure (P : GameParameters) : Prop :=
  SignatureFailure P ∨ HashFailure P ∨ TimelockFailure P ∨
    ChannelConservationFailure P

/-- The four assumptions, as a structure of proofs.  The game is safe exactly
under a value of this structure; every theorem that needs an assumption takes
it here rather than from the global environment. -/
structure Assumptions (P : GameParameters) : Prop where
  sigUnforgeable : Crypto.EufCma P.verify
  hashBinding : HashBinding P
  timelockEnforced : TimelockEnforced P
  channelConserved : ChannelConserved P

/-! ## 2. The finite game -/

/-- Who currently owns the contested output. -/
inductive Owner where
  | honest
  | adversary
deriving Repr, DecidableEq, BEq

/-- A commitment as it appears to the L1 finality rule.  `body` is the signed
commitment data; `preimage`/`paymentHash` are the HTLC binding carried by the
commitment.  The two fields are present so that both signature equivocation
(same signature, different body) and hash equivocation (same hash, different
preimage) can be stated concretely. -/
structure SignedCommitment where
  number : Nat
  body : ByteArray
  preimage : Preimage
  paymentHash : PaymentHash
  sig : EcdsaSig
deriving Repr, BEq

/-- The finite game state.  `finals` is the list of commitments the L1 layer
has accepted; `owner` is the contested output's owner; `height` is the L1
height and `expiry` is the contested output's timelock. -/
structure GameState where
  ledger : Ledger
  owner : Owner
  finals : List SignedCommitment
  height : Height
  expiry : Height

/-- The actions available to the adversary: network delivery, an off-chain
ledger operation, an L1 value-minting attempt, an L1 contested-output claim,
and an L1 commitment finalisation. -/
inductive Action where
  | noop
  | networkDeliver (tag : Nat)
  | ledgerOp (op : LedgerOp)
  | l1Mint (amount : Msat)
  | l1Claim (height : Height)
  | l1Finalize (commitment : SignedCommitment)

/-- The initial state: a conserving ledger, an honest contested-output owner,
no final commitments, height zero, and the parameter's expiry. -/
def initialState (P : GameParameters) : GameState where
  ledger :=
    { funding := ⟨P.funding⟩
      localBalance := ⟨P.localFunding⟩
      remoteBalance := ⟨P.remoteFunding⟩
      inFlight := ⟨0⟩
      fee := ⟨0⟩ }
  owner := .honest
  finals := []
  height := 0
  expiry := P.expiry

/-- Add `a` to the local balance, modelling the value-minting L1 attempt.  A
conserving ledger cannot be the source of this transition; that is exactly
what `ChannelConserved` refuses. -/
def mintLedger (l : Ledger) (a : Msat) : Ledger :=
  { l with localBalance := ⟨l.localBalance.val + a.val⟩ }

/-- A commitment is accepted for finalisation when its signature verifies
under the honest key and its preimage matches its payment hash. -/
def commitmentAccepted (P : GameParameters) (c : SignedCommitment) : Prop :=
  P.verify P.pk c.body c.sig = true ∧ P.hash c.preimage = c.paymentHash

instance commitmentAcceptedDecidable (P : GameParameters) (c : SignedCommitment) :
    Decidable (commitmentAccepted P c) := by
  unfold commitmentAccepted
  infer_instance

/-- One game step.  The L1 bridge decides whether an adversarial claim or
ledger transition is accepted; the primitive interface decides whether a
commitment is finalisable.  All partiality is kept in these Boolean guards,
so the transition function is total. -/
def step (P : GameParameters) (s : GameState) : Action → GameState
  | .noop => s
  | .networkDeliver _ => s
  | .ledgerOp op =>
      match s.ledger.step op with
      | some l' => { s with ledger := l' }
      | none => s
  | .l1Mint a =>
      let l' := mintLedger s.ledger a
      if P.acceptsLedger s.ledger l' = true then
        { s with ledger := l' }
      else s
  | .l1Claim h =>
      if h < s.expiry ∧ P.acceptsClaim h s.expiry = true then
        { s with owner := .adversary, height := Nat.max s.height h }
      else
        { s with height := Nat.max s.height h }
  | .l1Finalize c =>
      if commitmentAccepted P c then
        { s with finals := c :: s.finals }
      else s

/-- Value creation: the ledger's total exceeds the funding output. -/
def CreatesValue (s : GameState) : Prop :=
  s.ledger.funding.val < s.ledger.total

/-- The adversary owns the contested output. -/
def StealsContested (s : GameState) : Prop :=
  s.owner = .adversary

/-- Two final commitments equivocate: either one signature is valid for two
different bodies, or one payment hash is paired with two different
preimages. -/
def ConflictingFinals (s : GameState) : Prop :=
  (∃ c d : SignedCommitment,
      c ∈ s.finals ∧ d ∈ s.finals ∧ c.sig = d.sig ∧ c.body ≠ d.body) ∨
    (∃ c d : SignedCommitment,
      c ∈ s.finals ∧ d ∈ s.finals ∧
        c.paymentHash = d.paymentHash ∧ c.preimage ≠ d.preimage)

/-- The adversary's winning condition is the disjunction of the three bad
events. -/
def bad (s : GameState) : Prop :=
  CreatesValue s ∨ StealsContested s ∨ ConflictingFinals s

/-- Run a finite action sequence. -/
def runFrom (P : GameParameters) (s : GameState) : List Action → GameState
  | [] => s
  | a :: as => runFrom P (step P s a) as

/-- Run from the initial state. -/
def run (P : GameParameters) (actions : List Action) : GameState :=
  runFrom P (initialState P) actions

/-- A finite action sequence wins when it reaches a bad state. -/
def Wins (P : GameParameters) (actions : List Action) : Prop :=
  bad (run P actions)

/-- The adversary wins if some finite action sequence wins. -/
def AdversaryWins (P : GameParameters) : Prop :=
  ∃ actions : List Action, Wins P actions

/-! ## 3. The inductive invariant -/

/-- Every final commitment passed the signature and hash-binding checks. -/
def FinalsVerified (P : GameParameters) (s : GameState) : Prop :=
  ∀ c : SignedCommitment, c ∈ s.finals → commitmentAccepted P c

/-- The safety invariant maintained by every step under the four
assumptions: the ledger conserves value, the contested output is honest, and
every final commitment was properly verified. -/
def Safe (P : GameParameters) (s : GameState) : Prop :=
  s.ledger.Conserves ∧ s.owner = .honest ∧ FinalsVerified P s

theorem initialState_conserves (P : GameParameters) :
    (initialState P).ledger.Conserves := by
  unfold initialState Ledger.Conserves Ledger.total GameParameters.funding
  simp

theorem initial_safe (P : GameParameters) : Safe P (initialState P) := by
  refine ⟨initialState_conserves P, rfl, ?_⟩
  intro c hc
  simp [initialState] at hc

/-- **Every step preserves the safety invariant.**  The proof is the promised
case analysis over the six actions: `ledgerOp` uses
`Ledger.step_conserves`; `l1Mint` uses `ChannelConserved`; `l1Claim` uses
`TimelockEnforced`; `l1Finalize` uses the verification guard; `noop` and
`networkDeliver` are stuttering. -/
theorem step_safe (P : GameParameters) (A : Assumptions P) (s : GameState)
    (a : Action) (hs : Safe P s) : Safe P (step P s a) := by
  rcases hs with ⟨hcons, howner, hfin⟩
  cases a with
  | noop => exact ⟨hcons, howner, hfin⟩
  | networkDeliver tag => exact ⟨hcons, howner, hfin⟩
  | ledgerOp op =>
      show Safe P
        (match s.ledger.step op with
        | some l' => { s with ledger := l' }
        | none => s)
      split
      · rename_i l' hstep
        exact ⟨Ledger.step_conserves s.ledger l' op hcons hstep,
          howner, hfin⟩
      · exact ⟨hcons, howner, hfin⟩
  | l1Mint a =>
      show Safe P
        (let l' := mintLedger s.ledger a
         if P.acceptsLedger s.ledger l' = true then
           { s with ledger := l' }
         else s)
      dsimp only
      split
      · rename_i hacc
        exact ⟨A.channelConserved s.ledger (mintLedger s.ledger a) hacc hcons,
          howner, hfin⟩
      · exact ⟨hcons, howner, hfin⟩
  | l1Claim h =>
      show Safe P
        (if h < s.expiry ∧ P.acceptsClaim h s.expiry = true then
          { s with owner := .adversary, height := Nat.max s.height h }
         else
          { s with height := Nat.max s.height h })
      split
      · rename_i hcond
        exfalso
        exact (Nat.not_lt.mpr
          (A.timelockEnforced h s.expiry hcond.2)) hcond.1
      · exact ⟨hcons, howner, hfin⟩
  | l1Finalize c =>
      show Safe P
        (if commitmentAccepted P c then
          { s with finals := c :: s.finals }
         else s)
      split
      · rename_i hacc
        refine ⟨hcons, howner, ?_⟩
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hacc
        · exact hfin d hd
      · exact ⟨hcons, howner, hfin⟩

/-- The invariant is preserved by a finite run. -/
theorem runFrom_safe (P : GameParameters) (A : Assumptions P)
    (s : GameState) (hs : Safe P s) :
    ∀ actions : List Action, Safe P (runFrom P s actions)
  | [] => hs
  | a :: as => runFrom_safe P A (step P s a) (step_safe P A s a hs) as

/-- Every finite run from the initial state is safe. -/
theorem run_safe (P : GameParameters) (A : Assumptions P)
    (actions : List Action) : Safe P (run P actions) :=
  runFrom_safe P A (initialState P) (initial_safe P) actions

/-- **A safe state is not a bad state.**  Value creation contradicts
conservation, a stolen output contradicts honest ownership, and commitment
equivocation contradicts the verification history plus the signature and hash
assumptions. -/
theorem safe_not_bad (P : GameParameters) (A : Assumptions P) (s : GameState)
    (hs : Safe P s) : ¬ bad s := by
  rcases hs with ⟨hcons, howner, hfin⟩
  rintro (hval | hsteal | hconf)
  · unfold CreatesValue at hval
    unfold Ledger.Conserves at hcons
    omega
  · unfold StealsContested at hsteal
    rw [howner] at hsteal
    cases hsteal
  · have hcoh : ∀ c d : SignedCommitment,
        c ∈ s.finals → d ∈ s.finals →
          (c.sig = d.sig → c.body = d.body) ∧
            (c.paymentHash = d.paymentHash → c.preimage = d.preimage) := by
      intro c d hc hd
      have hc' := hfin c hc
      have hd' := hfin d hd
      constructor
      · intro hsig
        have hd1 : P.verify P.pk d.body c.sig = true := by
          simpa [hsig] using hd'.1
        exact A.sigUnforgeable P.pk c.body d.body c.sig hc'.1 hd1
      · intro hhash
        have hch : P.hash c.preimage = P.hash d.preimage := by
          rw [hc'.2, hhash, ← hd'.2]
        exact A.hashBinding c.preimage d.preimage hch
    rcases hconf with
      ⟨c, d, hc, hd, hsig, hbody⟩ | ⟨c, d, hc, hd, hhash, hpre⟩
    · exact hbody ((hcoh c d hc hd).1 hsig)
    · exact hpre ((hcoh c d hc hd).2 hhash)

/-- **Safety theorem.**  Under the four explicit assumptions, no finite
adversarial action sequence reaches a bad state. -/
theorem safe_of_assumptions (P : GameParameters) (A : Assumptions P) :
    ∀ actions : List Action, ¬ Wins P actions := by
  intro actions
  exact safe_not_bad P A (run P actions) (run_safe P A actions)

/-- **Main reduction.**  If the adversary wins some finite game, at least one
of the four named assumptions has failed.  This is the disjunction of
assumption failures required by the mission, and it is not a new axiom: it is
the contrapositive of `safe_of_assumptions`. -/
theorem adversary_win_implies_assumption_failure (P : GameParameters) :
    AdversaryWins P → AssumptionFailure P := by
  intro hw
  apply Classical.byContradiction
  intro h
  have hsig : Crypto.EufCma P.verify := by
    apply Classical.byContradiction
    intro hbad
    exact h (Or.inl hbad)
  have hhash : HashBinding P := by
    apply Classical.byContradiction
    intro hbad
    exact h (Or.inr (Or.inl hbad))
  have htl : TimelockEnforced P := by
    apply Classical.byContradiction
    intro hbad
    exact h (Or.inr (Or.inr (Or.inl hbad)))
  have hcons : ChannelConserved P := by
    apply Classical.byContradiction
    intro hbad
    exact h (Or.inr (Or.inr (Or.inr hbad)))
  rcases hw with ⟨actions, hwin⟩
  exact safe_of_assumptions P ⟨hsig, hhash, htl, hcons⟩ actions hwin

/-! ## 4. Bridge to the wave-A `SecurityGame` -/

/-- Prepend the action chosen at step `n` to the trace of the first `n`
actions.  This is the finite action list induced by a deterministic
adversarial strategy. -/
def actionTrace (P : GameParameters)
    (strategy : Nat → GameState → Action) : Nat → List Action
  | 0 => []
  | n + 1 =>
      actionTrace P strategy n ++
        [strategy n (run P (actionTrace P strategy n))]

theorem runFrom_append (P : GameParameters) (s : GameState)
    (xs ys : List Action) :
    runFrom P s (xs ++ ys) = runFrom P (runFrom P s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => simp [runFrom, ih]

theorem runFrom_snoc (P : GameParameters) (s : GameState)
    (xs : List Action) (a : Action) :
    runFrom P s (xs ++ [a]) = step P (runFrom P s xs) a := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih => simp [runFrom, ih]

theorem run_snoc (P : GameParameters) (xs : List Action) (a : Action) :
    run P (xs ++ [a]) = step P (run P xs) a := by
  unfold run
  exact runFrom_snoc P (initialState P) xs a

/-- The wave-A game induced by a deterministic action strategy.  The wave-A
`Adversary` record is carried unchanged; only its strategy is compressed
into `strategy`, because the action alphabet of this module is finite. -/
def toSecurityGame (P : GameParameters)
    (strategy : Nat → GameState → Action) (adv : LnLean.Security.Adversary) :
    LnLean.Security.SecurityGame GameState where
  adversary := adv
  init := initialState P
  step := fun s _ n => step P s (strategy n s)
  bad := bad
  honest := []

theorem securityGame_run_eq (P : GameParameters)
    (strategy : Nat → GameState → Action) (adv : LnLean.Security.Adversary) :
    ∀ n : Nat,
      (toSecurityGame P strategy adv).run n =
        run P (actionTrace P strategy n)
  | 0 => rfl
  | n + 1 => by
      rw [LnLean.Security.SecurityGame.run_succ]
      rw [securityGame_run_eq P strategy adv n]
      change step P (run P (actionTrace P strategy n))
          (strategy n (run P (actionTrace P strategy n))) =
        run P (actionTrace P strategy n ++
          [strategy n (run P (actionTrace P strategy n))])
      rw [run_snoc]

/-- **Wave-A form of the reduction.**  A bad state reached by the wave-A
`SecurityGame` at horizon `n` also implies an assumption failure.  This
connects the finite game of this module to the shared threat-model record
without changing that record. -/
theorem securityGame_win_implies_failure (P : GameParameters)
    (strategy : Nat → GameState → Action)
    (adv : LnLean.Security.Adversary) (n : Nat)
    (h : LnLean.Security.AdversaryWins
      (toSecurityGame P strategy adv) n) :
    AssumptionFailure P := by
  have h' : (toSecurityGame P strategy adv).bad
      ((toSecurityGame P strategy adv).run n) := by
    simpa [LnLean.Security.AdversaryWins] using h
  change bad ((toSecurityGame P strategy adv).run n) at h'
  rw [securityGame_run_eq P strategy adv n] at h'
  exact adversary_win_implies_assumption_failure P
    ⟨actionTrace P strategy n, h'⟩


/-! ## 5. Non-vacuity: a concrete safe instance -/

/-- A concrete parameter set on which all four assumptions hold: verification
never accepts, the hash is the identity on preimages, and the L1 bridge
accepts nothing.  The honest opening balances add up to the funding value. -/
def safeParameters : GameParameters where
  verify := fun _ _ _ => false
  hash := fun p => ⟨p.bytes⟩
  acceptsClaim := fun _ _ => false
  acceptsLedger := fun _ _ => false
  pk := ⟨ByteArray.empty⟩
  localFunding := 60000
  remoteFunding := 40000
  expiry := 144

theorem safeParameters_assumptions : Assumptions safeParameters := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pk m1 m2 s h1 h2
    simp [safeParameters] at h1
  · intro p q h
    have hb : p.bytes = q.bytes := by simpa [safeParameters] using h
    cases p
    cases q
    simpa using hb
  · intro h e hacc
    simp [safeParameters] at hacc
  · intro l l' hacc hcons
    simp [safeParameters] at hacc

/-- **The concrete instance is secure.**  No finite action sequence wins on
`safeParameters`, so the reduction's conclusion is not forced by a
degenerate game. -/
theorem safeParameters_no_win : ¬ AdversaryWins safeParameters := by
  intro hw
  rcases hw with ⟨actions, hwin⟩
  exact safe_of_assumptions safeParameters safeParameters_assumptions
    actions hwin

/-- The reduction applies to the concrete instance as well: because it is
secure, no winning strategy exists, and the implication is vacuously true.
This is recorded to show the concrete game and the abstract game share the
same definitions. -/
theorem safeParameters_win_implies_failure :
    AdversaryWins safeParameters → AssumptionFailure safeParameters :=
  adversary_win_implies_assumption_failure safeParameters

/-- A broken parameter set: the L1 bridge accepts every ledger transition,
so a minting transition is available.  It is used to show that the reduction
is not vacuous in the winning direction. -/
def brokenParameters : GameParameters :=
  { safeParameters with acceptsLedger := fun _ _ => true }

theorem brokenParameters_conservationFailure :
    ChannelConservationFailure brokenParameters := by
  intro h
  let l : Ledger :=
    { funding := ⟨0⟩, localBalance := ⟨0⟩, remoteBalance := ⟨0⟩,
      inFlight := ⟨0⟩, fee := ⟨0⟩ }
  have hc : l.Conserves := by
    unfold l Ledger.Conserves Ledger.total
    simp
  have hacc : brokenParameters.acceptsLedger l (mintLedger l ⟨1⟩) = true := by
    simp [brokenParameters]
  have h' := h l (mintLedger l ⟨1⟩) hacc hc
  unfold mintLedger Ledger.Conserves Ledger.total at h'
  simp at h'

theorem brokenParameters_wins : AdversaryWins brokenParameters := by
  refine ⟨[Action.l1Mint ⟨1⟩], ?_⟩
  unfold Wins bad
  left
  show CreatesValue (run brokenParameters [Action.l1Mint ⟨1⟩])
  simp [CreatesValue, run, runFrom, step, mintLedger, initialState,
    GameParameters.funding, Ledger.total, brokenParameters, safeParameters]

/-- The broken instance reaches the reduction's conclusion by actually
winning: this is the non-vacuous direction of the main theorem. -/
theorem brokenParameters_win_implies_failure :
    AdversaryWins brokenParameters → AssumptionFailure brokenParameters :=
  adversary_win_implies_assumption_failure brokenParameters


end LnLean.Proofs.PhaseC3.SecurityGame
