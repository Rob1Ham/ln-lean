import LnLean.Channel.Penalty
import LnLean.Proofs.Channel.PenaltyProps

/-!
# LnLean.Proofs.PhaseC2.PenaltyDoubleSpend

English claim.  Compose the penalty model of `LnLean.Channel.Penalty` into an
exclusive-spend theorem.  A `PenaltyTx` that is valid for a revoked
commitment (`punishable`) spends *both* contested commitment outputs, and,
once the same penalty transaction is confirmed in time, no transaction that
spends either contested outpoint is accepted by the same L1 bridge, except
the penalty transaction itself.

The module states the result twice.

1. Against the existing `LnLean.Channel.L1ScriptBridge` this yields the
   no-breacher-spend conclusion.  That bridge is, however, self-refuting: its
   `noDoubleSpend` field quantifies over the *same* transaction as well as
   distinct ones, so no confirmed transaction may spend an outpoint at all.
   The theorem `bridge_not_confirms_spending` records this and the report
   records it as a newly discovered gap.  The existing theorem remains true,
   but it is vacuous.
2. Against an explicit non-vacuous bridge, `L1ScriptBridgeDistinct`, whose
   no-double-spend field is restricted to distinct transactions, the module
   proves the strongest true form: the penalty transaction is the unique
   confirmed spend of either contested outpoint.  `singletonBridge` shows
   that this bridge can confirm a transaction, so the statement is not
   vacuous.

The bridge is an explicit structure argument throughout; script execution,
signature checking and the revocation witness are not formalised.

BOLT anchors.
* BOLT 5 revoked transaction close handling:
  `refs/bolts/05-onchain.md:510` (spend the remote main output and every
  revoked HTLC output with the revocation key; one transaction may resolve
  all outputs), `:517` (the penalty transaction inputs/outputs), `:545`
  (one transaction may resolve all revoked outputs), `:582` (penalty
  transaction weight).
* BOLT 3 `to_local` output and revocation branch:
  `refs/bolts/03-transactions.md:113`; `to_remote` output:
  `refs/bolts/03-transactions.md:136`; `revocationpubkey` derivation:
  `refs/bolts/03-transactions.md:799`.

rust-lightning anchors (commit fe49009).
* `lightning/src/ln/chan_utils.rs:687`
  (`get_revokeable_redeemscript`, the `to_local` script with the revocation
  key branch).
* `lightning/src/ln/chan_utils.rs:763` (HTLC output script with the
  revocation branch).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`, used by the punisher).
* `lightning/src/ln/chan_utils.rs:2183` (`revokeable_output_index`) and
  `:2208` (`build_to_local_justice_tx`).
* `lightning/src/chain/channelmonitor.rs:5079`
  (`check_spend_counterparty_transaction`, the revoked-commitment path).

Not modelled.
* Bitcoin script execution and signature checking.  The L1 consequence is
  the explicit bridge structure, not a script-semantics theorem.
* Fee bumping, package relay, pinning, and the economics of the penalty fee.
* Watchtower liveness.  The timely confirmation is a hypothesis inside
  `penaltyValid`.
* HTLC-output penalties; `PenaltyTx` covers the two main outputs only.
* Concrete shachain/secp256k1 arithmetic; `RevocationScheme` is a parameter.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Channel
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## Contested outputs and the punishability projection -/

/-- The two outpoints contested by a revoked commitment: its old `to_local`
and `to_remote` outputs. -/
def ContestedOutpoint (c : RevokedCommitment) (o : OutPoint) : Prop :=
  o = c.toLocal ∨ o = c.toRemote

/-- The old `to_local` outpoint is contested. -/
theorem contestedOutpoint_toLocal (c : RevokedCommitment) :
    ContestedOutpoint c c.toLocal :=
  Or.inl rfl

/-- The old `to_remote` outpoint is contested. -/
theorem contestedOutpoint_toRemote (c : RevokedCommitment) :
    ContestedOutpoint c c.toRemote :=
  Or.inr rfl

/-- `punishable` contains the underlying `penaltyValid` certificate. -/
theorem punishable_valid {scheme : RevocationScheme} {c : RevokedCommitment}
    {p : PenaltyTx} {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (h : punishable scheme c p w confirm window) :
    penaltyValid scheme c p w confirm window :=
  h.2

/-- A punishable penalty transaction spends both contested outputs.  This is
the first half of the exclusive-spend theorem, obtained by composing
`penaltyValid_spends` with the two existing spend projections. -/
theorem punishable_spends_both {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : punishable scheme c p w confirm window) :
    Spends p.toTx c.toLocal ∧ Spends p.toTx c.toRemote :=
  ⟨LnLean.Proofs.Channel.penaltyValid_spends_toLocal (punishable_valid h),
    LnLean.Proofs.Channel.penaltyValid_spends_toRemote (punishable_valid h)⟩

/-- A punishable penalty transaction spends every contested outpoint. -/
theorem punishable_spends_contested {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : punishable scheme c p w confirm window) {o : OutPoint}
    (ho : ContestedOutpoint c o) : Spends p.toTx o := by
  rcases ho with rfl | rfl
  · exact (punishable_spends_both h).1
  · exact (punishable_spends_both h).2

/-- The confirmation height of a punishable penalty transaction lies in the
open punishment window; this is the "timely confirmation" part of the
composition. -/
theorem punishable_timely {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : punishable scheme c p w confirm window) :
    c.breachHeight ≤ confirm ∧ confirm < c.breachHeight + window :=
  penaltyValid_timely (punishable_valid h)

/-- The revocation-key equality that `punishable` carries.  It is an explicit
hypothesis of the model, not a global cryptographic assumption. -/
theorem punishable_revocation_key {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : punishable scheme c p w confirm window) :
    deriveRevocationPubkey scheme w.revocationBase (scheme.pointOf w.secret) =
      scheme.derivePrivkey w.revocationBase w.secret :=
  penaltyValid_key (punishable_valid h)

/-! ## The existing bridge is vacuous

`L1ScriptBridge.noDoubleSpend` is quantified over all transaction pairs,
including the pair `(t, t)`.  Applying it reflexively shows that a confirmed
transaction cannot spend *any* outpoint.  The existing no-breacher-spend
theorems are therefore true for the wrong reason; the non-vacuous development
below uses `L1ScriptBridgeDistinct`.
-/

/-- No transaction accepted by an existing `L1ScriptBridge` may spend an
outpoint, because the bridge also forbids the transaction to conflict with
itself. -/
theorem bridge_not_confirms_spending (bridge : L1ScriptBridge) {t : Tx}
    {o : OutPoint} (h : Spends t o) : ¬ bridge.confirms t := by
  intro hconf
  exact bridge.noDoubleSpend t t o h h hconf hconf

/-- A confirmed penalty transaction is impossible against the existing
bridge, since `p.toTx` spends `p.inputLocal`. -/
theorem bridge_confirmation_inconsistent (bridge : L1ScriptBridge)
    (p : PenaltyTx) (hconf : bridge.confirms p.toTx) : False :=
  bridge_not_confirms_spending bridge (PenaltyTx.spends_inputLocal p) hconf

/-- In particular, the existing bridge never confirms a penalty
transaction.  This is the precise sense in which the old interface is
vacuous, and it is the counterexample record for the bridge gap. -/
theorem no_bridge_confirms_penalty (p : PenaltyTx) (bridge : L1ScriptBridge) :
    ¬ bridge.confirms p.toTx :=
  bridge_not_confirms_spending bridge (PenaltyTx.spends_inputLocal p)

/-- **Composition against the existing bridge.**  A punishable penalty spends
both contested outputs and, after its confirmation, no `BreacherSpend` of
either output is accepted by the same bridge.  The confirmation hypothesis is
kept explicit to match the mission statement; `bridge_confirmation_inconsistent`
shows that it is unsatisfiable, so the second conjunct also follows
unconditionally (`punishable_exclusive_spend_unconditional`). -/
theorem punishable_exclusive_spend (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) :
    (Spends p.toTx c.toLocal ∧ Spends p.toTx c.toRemote) ∧
      (∀ b : Tx, BreacherSpend c b → ¬ bridge.confirms b) :=
  ⟨punishable_spends_both hp,
    fun b hb =>
      punished_not_breacher_spendable bridge scheme c p w confirm window b
        (punishable_valid hp) hb hconf⟩

/-- The same exclusion without using the unsatisfiable confirmation
hypothesis.  It holds because the existing bridge confirms no spending
transaction at all. -/
theorem punishable_exclusive_spend_unconditional (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window) :
    (Spends p.toTx c.toLocal ∧ Spends p.toTx c.toRemote) ∧
      (∀ b : Tx, BreacherSpend c b → ¬ bridge.confirms b) := by
  refine ⟨punishable_spends_both hp, ?_⟩
  intro b hb
  rcases hb with hlocal | hremote
  · exact bridge_not_confirms_spending bridge hlocal
  · exact bridge_not_confirms_spending bridge hremote

/-! ## A non-vacuous L1 bridge and the exclusive-spend theorem -/

/-- The L1 bridge with the intended no-double-spend assumption: two
*confirmed distinct* transactions cannot spend the same outpoint.  This is
the standard L1 consensus fact and, unlike `L1ScriptBridge`, it is consistent
with a confirmed spending transaction. -/
structure L1ScriptBridgeDistinct where
  /-- The (abstract) L1 confirmation predicate. -/
  confirms : Tx → Prop
  /-- Distinct confirmed transactions cannot spend the same outpoint. -/
  noDoubleSpend : ∀ (t u : Tx) (o : OutPoint), t ≠ u →
    Spends t o → Spends u o → confirms t → ¬ confirms u

/-- The existing, stronger bridge implies the distinct-transaction bridge.
This is a one-way refinement: the converse is not available, and the
existing bridge additionally rules out every confirmed spend. -/
def bridgeToDistinct (bridge : L1ScriptBridge) : L1ScriptBridgeDistinct where
  confirms := bridge.confirms
  noDoubleSpend := fun t u o _ ht hu htc huc =>
    bridge.noDoubleSpend t u o ht hu htc huc

/-- `ExclusiveSpend bridge c p` says that the penalty transaction `p` is
confirmed and is the *only* confirmed spend of either contested outpoint.
This is the strongest exclusive-spend conclusion available under
`L1ScriptBridgeDistinct`: an accepted breacher spend must literally be the
penalty transaction. -/
def ExclusiveSpend (bridge : L1ScriptBridgeDistinct) (c : RevokedCommitment)
    (p : PenaltyTx) : Prop :=
  bridge.confirms p.toTx ∧
    ∀ b : Tx, BreacherSpend c b → bridge.confirms b → b = p.toTx

/-- **Exclusive-spend theorem.**  Let `p` be a valid penalty transaction for
a revoked commitment and suppose the same bridge confirms `p.toTx` after its
timely window.  Then `p` spends both contested outputs and is the unique
confirmed spend of either output.  In particular, no *other* `BreacherSpend`
is accepted. -/
theorem punishable_exclusive_spend_distinct (bridge : L1ScriptBridgeDistinct)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) :
    (Spends p.toTx c.toLocal ∧ Spends p.toTx c.toRemote) ∧
      ExclusiveSpend bridge c p := by
  refine ⟨punishable_spends_both hp, hconf, ?_⟩
  intro b hb hbc
  by_cases hne : b = p.toTx
  · exact hne
  · exfalso
    rcases hb with hlocal | hremote
    · exact (bridge.noDoubleSpend b p.toTx c.toLocal hne hlocal
        (LnLean.Proofs.Channel.penaltyValid_spends_toLocal (punishable_valid hp))
        hbc) hconf
    · exact (bridge.noDoubleSpend b p.toTx c.toRemote hne hremote
        (LnLean.Proofs.Channel.penaltyValid_spends_toRemote (punishable_valid hp))
        hbc) hconf

/-- Any confirmed breacher spend of a contested output is exactly the
penalty transaction. -/
theorem confirmed_breacher_spend_eq_penalty (bridge : L1ScriptBridgeDistinct)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) (b : Tx)
    (hb : BreacherSpend c b) (hbc : bridge.confirms b) : b = p.toTx :=
  (punishable_exclusive_spend_distinct bridge scheme c p w confirm window hp
    hconf).2.2 b hb hbc

/-- No transaction different from the penalty transaction is accepted as a
breacher spend of either contested outpoint. -/
theorem no_other_breacher_spend_confirmed (bridge : L1ScriptBridgeDistinct)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) (b : Tx)
    (hb : BreacherSpend c b) (hne : b ≠ p.toTx) :
    ¬ bridge.confirms b := by
  intro hbc
  exact hne (confirmed_breacher_spend_eq_penalty bridge scheme c p w confirm
    window hp hconf b hb hbc)

/-- The `to_local` half of the non-vacuous exclusion. -/
theorem no_other_toLocal_spend_confirmed (bridge : L1ScriptBridgeDistinct)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) (b : Tx)
    (hb : Spends b c.toLocal) (hne : b ≠ p.toTx) :
    ¬ bridge.confirms b :=
  no_other_breacher_spend_confirmed bridge scheme c p w confirm window hp hconf
    b (Or.inl hb) hne

/-- The `to_remote` half of the non-vacuous exclusion. -/
theorem no_other_toRemote_spend_confirmed (bridge : L1ScriptBridgeDistinct)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hp : punishable scheme c p w confirm window)
    (hconf : bridge.confirms p.toTx) (b : Tx)
    (hb : Spends b c.toRemote) (hne : b ≠ p.toTx) :
    ¬ bridge.confirms b :=
  no_other_breacher_spend_confirmed bridge scheme c p w confirm window hp hconf
    b (Or.inr hb) hne

/-! ## Non-vacuity of the distinct bridge -/

/-- A bridge that confirms exactly one chosen transaction.  Its no-double-
spend field holds because two confirmed transactions are both equal to the
chosen one.  This witnesses that `L1ScriptBridgeDistinct` can accept spends
and is therefore not vacuous. -/
def singletonBridge (s : Tx) : L1ScriptBridgeDistinct where
  confirms := fun u => u = s
  noDoubleSpend := by
    intro t u _o hne _ht _hu htc huc
    exact hne (htc.trans huc.symm)

/-- The singleton bridge confirms its chosen transaction. -/
theorem singletonBridge_confirms (s : Tx) :
    (singletonBridge s).confirms s :=
  rfl

/-- For every penalty transaction there is a non-vacuous bridge that accepts
it.  This is the existence counterpart to
`no_bridge_confirms_penalty`: the intended bridge semantics is satisfiable,
the existing self-refuting one is not. -/
theorem exists_distinctBridge_confirms_penalty (p : PenaltyTx) :
    ∃ bridge : L1ScriptBridgeDistinct, bridge.confirms p.toTx :=
  ⟨singletonBridge p.toTx, rfl⟩

end LnLean.Proofs.PhaseC2
