import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Channel.Revocation

/-!
# LnLean.Channel.Penalty

English claim.  When a party broadcasts a revoked commitment transaction,
the counterparty can spend *both* old outputs (the revoked `to_local` output
and the revoked `to_remote` output) with the revocation key derived from the
revealed per-commitment secret, sweeping their total value into one output.
We model the penalty transaction, the predicate that it is a valid punishment
(breach, matching revocation key, both inputs, one sweep output, timely L1
confirmation), and two obligations:

1. every old commitment is punishable given its revocation secret and a
   timely L1 confirmation;
2. a punished commitment cannot also be spent by the breacher.

Obligation 2 is stated relative to a named L1 bridge, `L1ScriptBridge`, whose
`noDoubleSpend` field is the L1 consensus fact that two confirmed transactions
cannot spend the same outpoint.  Script execution itself is not formalised
here; the bridge is the explicit interface.

BOLT anchors.
* BOLT 5 revoked transaction close handling: `refs/bolts/05-onchain.md:510`
  (spend the remote main output and every revoked HTLC output with the
  revocation key; a single penalty transaction may resolve all outputs).
* BOLT 5 penalty transaction weight: `refs/bolts/05-onchain.md:582`.
* BOLT 3 `to_local` output and revocation branch:
  `refs/bolts/03-transactions.md:113`;
  `to_remote` output: `refs/bolts/03-transactions.md:136`.
* BOLT 3 `revocationpubkey` derivation: `refs/bolts/03-transactions.md:799`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:687` (`get_revokeable_redeemscript`,
  the `to_local` script with the revocation key branch).
* `lightning/src/ln/chan_utils.rs:763` (HTLC output script with the
  revocation branch).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`, used by the punisher).
* `lightning/src/ln/channel.rs:6258` (comment on revoking an old commitment
  by revealing the corresponding `per_commitment_secret`).

Not modelled.
* Bitcoin script execution and signature checking.  The bridge supplies
  only the no-double-spend consequence.
* Fee bumping, package relay, pinning, and the economics of penalty
  transaction fees (BOLT 5 is a recommendation, not consensus).
* Watchtower liveness: a timely confirmation is a hypothesis.
* HTLC-output penalties are represented only through the two main outputs;
  the generalisation to per-HTLC second-stage transactions is a follow-up
  obligation.
-/

namespace LnLean.Channel

open LnLean
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## The revoked commitment and the penalty transaction -/

/-- The two main outputs of one old commitment transaction, with the values
that the penalty transaction sweeps.  HTLC outputs are excluded from this
scaffold (see the module note). -/
structure RevokedCommitment where
  /-- The commitment number of the published (old) transaction. -/
  number : Nat
  /-- The current commitment number of the channel. -/
  currentNumber : Nat
  /-- Outpoint of the old `to_local` output. -/
  toLocal : OutPoint
  /-- Outpoint of the old `to_remote` output. -/
  toRemote : OutPoint
  /-- Value of the old `to_local` output. -/
  toLocalValue : BtcAmount
  /-- Value of the old `to_remote` output. -/
  toRemoteValue : BtcAmount
  /-- Height at which the revoked commitment was observed on chain. -/
  breachHeight : Height
  /-- Fee paid by the penalty transaction. -/
  penaltyFee : BtcAmount
deriving Repr

/-- A commitment is a breach exactly when its number is strictly below the
current commitment number.  BOLT 5: any previous commitment besides the most
current one is revoked (`refs/bolts/05-onchain.md:512`). -/
def breachDetected (c : RevokedCommitment) : Prop := c.number < c.currentNumber

/-- BOLT 5 penalty transaction: one input per old main output and exactly one
sweep output.  `refs/bolts/05-onchain.md:517`. -/
structure PenaltyTx where
  inputLocal : OutPoint
  inputRemote : OutPoint
  sweep : TxOut
deriving Repr

/-- The L1 transaction corresponding to a penalty transaction: version 2,
two inputs, one output, locktime 0. -/
def PenaltyTx.toTx (p : PenaltyTx) : Tx :=
  { version := 2
    vin :=
      [ { prevout := p.inputLocal, scriptSig := Bitcoin.Data.Script.empty, sequence := 0xFFFFFFFF }
      , { prevout := p.inputRemote, scriptSig := Bitcoin.Data.Script.empty, sequence := 0xFFFFFFFF } ]
    vout := [p.sweep]
    locktime := 0
    witness := [[], []] }

/-- L1 spends outpoint `o`. -/
def Spends (tx : Tx) (o : OutPoint) : Prop :=
  ∃ i : TxIn, i ∈ tx.vin ∧ i.prevout = o

/-- The penalty transaction consumes both old outputs. -/
def penaltySpendsBoth (c : RevokedCommitment) (p : PenaltyTx) : Prop :=
  p.inputLocal = c.toLocal ∧ p.inputRemote = c.toRemote

/-- The breacher's alternative spend of one of the old outputs. -/
def BreacherSpend (c : RevokedCommitment) (tx : Tx) : Prop :=
  Spends tx c.toLocal ∨ Spends tx c.toRemote

/-- A confirmation is timely if it occurs within `window` blocks after the
breach was observed.  The revocation branch has no CSV delay, so this is
the only timing condition of the model. -/
def timelyL1Confirmation (breach confirm : Height) (window : Blocks) : Prop :=
  breach ≤ confirm ∧ confirm < breach + window

/-- The witness material the punisher holds: the revealed per-commitment
secret and its own revocation basepoint. -/
structure PenaltyWitness where
  secret : PerCommitmentSecret
  revocationBase : PubKey
deriving Repr

/-- A valid punishment: the published commitment is old, the revealed secret
derives the revocation key that locks the old outputs, the transaction spends
both outputs, sweeps their total value minus the fee, and confirms in time.
The key-derivation equality is the *conditional* cryptographic premise: it is
discharged by `RevocationScheme.consistent`, not assumed globally. -/
def penaltyValid (scheme : RevocationScheme) (c : RevokedCommitment)
    (p : PenaltyTx) (w : PenaltyWitness) (confirm : Height) (window : Blocks) : Prop :=
  breachDetected c ∧
  deriveRevocationPubkey scheme w.revocationBase (scheme.pointOf w.secret) =
    scheme.derivePrivkey w.revocationBase w.secret ∧
  penaltySpendsBoth c p ∧
  p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee ∧
  timelyL1Confirmation c.breachHeight confirm window

/-- `punishable` is the protocol-level predicate: a breach plus a valid
penalty transaction. -/
def punishable (scheme : RevocationScheme) (c : RevokedCommitment)
    (p : PenaltyTx) (w : PenaltyWitness) (confirm : Height) (window : Blocks) : Prop :=
  breachDetected c ∧ penaltyValid scheme c p w confirm window

/-! ## Structural facts -/

theorem breachDetected_iff (c : RevokedCommitment) :
    breachDetected c ↔ c.number < c.currentNumber := Iff.rfl

theorem penaltyTx_toTx_vin (p : PenaltyTx) : p.toTx.vin.length = 2 := rfl

theorem penaltyTx_toTx_vout (p : PenaltyTx) : p.toTx.vout.length = 1 := rfl

/-- The penalty transaction spends its `inputLocal` outpoint. -/
theorem PenaltyTx.spends_inputLocal (p : PenaltyTx) : Spends p.toTx p.inputLocal := by
  refine ⟨{ prevout := p.inputLocal, scriptSig := Bitcoin.Data.Script.empty, sequence := 0xFFFFFFFF },
    ?_, rfl⟩
  simp [PenaltyTx.toTx]

/-- The penalty transaction spends its `inputRemote` outpoint. -/
theorem PenaltyTx.spends_inputRemote (p : PenaltyTx) : Spends p.toTx p.inputRemote := by
  refine ⟨{ prevout := p.inputRemote, scriptSig := Bitcoin.Data.Script.empty, sequence := 0xFFFFFFFF },
    ?_, rfl⟩
  simp [PenaltyTx.toTx]

/-- A tx that spends both named outpoints spends the old `to_local` output. -/
theorem penalty_spends_toLocal {c : RevokedCommitment} {p : PenaltyTx}
    (h : penaltySpendsBoth c p) : Spends p.toTx c.toLocal := by
  rcases h with ⟨h1, _⟩
  rw [← h1]
  exact p.spends_inputLocal

/-- A tx that spends both named outpoints spends the old `to_remote` output. -/
theorem penalty_spends_toRemote {c : RevokedCommitment} {p : PenaltyTx}
    (h : penaltySpendsBoth c p) : Spends p.toTx c.toRemote := by
  rcases h with ⟨_, h2⟩
  rw [← h2]
  exact p.spends_inputRemote

theorem penaltyValid_breach {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) : breachDetected c := h.1

theorem penaltyValid_key {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    deriveRevocationPubkey scheme w.revocationBase (scheme.pointOf w.secret) =
      scheme.derivePrivkey w.revocationBase w.secret := h.2.1

theorem penaltyValid_spends {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) : penaltySpendsBoth c p := h.2.2.1

theorem penaltyValid_sweep {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee := h.2.2.2.1

theorem penaltyValid_timely {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    timelyL1Confirmation c.breachHeight confirm window := h.2.2.2.2

/-! ## The named L1 bridge -/

/-- The only L1 fact the penalty safety statement needs: a confirmed
transaction's inputs cannot be confirmed again by another transaction.
Script execution, signatures and the revocation witness are abstracted by
`confirms`; this is the explicit bridge named by the module contract. -/
structure L1ScriptBridge where
  /-- The (abstract) L1 confirmation predicate. -/
  confirms : Tx → Prop
  /-- No two confirmed transactions spend the same outpoint. -/
  noDoubleSpend : ∀ (t u : Tx) (o : OutPoint),
    Spends t o → Spends u o → confirms t → ¬ confirms u

/-! ## The two penalty obligations, as `Prop`s -/

/-- **Obligation LN-PENALTY-PUNISH.**  Every old commitment is punishable
given its revocation secret and a timely L1 confirmation. -/
def PenaltyObligationPunishable : Prop :=
  ∀ (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks),
    breachDetected c →
    deriveRevocationPubkey scheme w.revocationBase (scheme.pointOf w.secret) =
      scheme.derivePrivkey w.revocationBase w.secret →
    penaltySpendsBoth c p →
    p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee →
    timelyL1Confirmation c.breachHeight confirm window →
    punishable scheme c p w confirm window

/-- The first penalty obligation holds structurally: its hypotheses are
exactly the conjuncts of `punishable`.  Cryptographic soundness is the
scheme hypothesis, not a global assumption. -/
theorem penaltyObligation_punishable : PenaltyObligationPunishable := by
  intro scheme c p w confirm window hbreach hkey hspend hsweep htimely
  exact ⟨hbreach, hbreach, hkey, hspend, hsweep, htimely⟩

/-- **Obligation LN-PENALTY-NO-DOUBLE-SPEND.**  A punished commitment cannot
also be spent by the breacher, relative to the named L1 bridge. -/
def PenaltyObligationNoBreacherSpend : Prop :=
  ∀ (bridge : L1ScriptBridge) (c : RevokedCommitment) (p : PenaltyTx) (b : Tx),
    penaltySpendsBoth c p →
    BreacherSpend c b →
    bridge.confirms p.toTx →
    ¬ bridge.confirms b

/-- The second penalty obligation follows from L1 no-double-spend: the
confirmed penalty transaction and the breacher's transaction would spend the
same old outpoint. -/
theorem penaltyObligation_no_breacher_spend : PenaltyObligationNoBreacherSpend := by
  intro bridge c p b hspend hbreach hconf hbconf
  rcases hbreach with hb | hb
  · exact bridge.noDoubleSpend p.toTx b c.toLocal
      (penalty_spends_toLocal hspend) hb hconf hbconf
  · exact bridge.noDoubleSpend p.toTx b c.toRemote
      (penalty_spends_toRemote hspend) hb hconf hbconf

/-- Direct statement of the no-double-spend consequence for a valid penalty. -/
theorem punished_not_breacher_spendable (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hv : penaltyValid scheme c p w confirm window)
    (hb : BreacherSpend c b) (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  penaltyObligation_no_breacher_spend bridge c p b (penaltyValid_spends hv) hb hconf

end LnLean.Channel
