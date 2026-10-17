import LnLean

/-!
# LnLean.Proofs.PhaseC2.PenaltyBridge

English claim.  After a breach the honest party's penalty transaction
`p.toTx` spends both contested outputs of the revoked commitment,
`c.toLocal` and `c.toRemote`, and pays a *single* output `p.sweep` whose
script is controlled by the honest party.  Its value is exactly the sum of
the two contested values minus the penalty fee; with a non-negative fee it is
bounded above by that sum, and with a fee no larger than the sum it is also
non-negative.

The L1 side is an explicit `PenaltyL1Bridge` with a `spends` relation and an
`accepted` predicate.  The two L1 obligations used by the penalty path are
*fields of the structure*, never axioms:

* `penaltyAccepted` — every model-valid penalty transaction is accepted by
  L1 (the script/witness acceptance bridge);
* `sweepControlled` — the single sweep output is controlled by the honest
  party.

The no-double-spend field is stated for *distinct* transactions.  This is
the strongest true form: a transaction trivially shares its own outpoints, so
the same-transaction case in `LnLean.Channel.L1ScriptBridge.noDoubleSpend`
makes that source bridge accept nothing (see
`l1ScriptBridge_no_confirmed_spend` below).  The corrected field still gives
the exclusive-spend composition: any *other* accepted transaction that
spends a contested output is impossible; an accepted transaction that does
spend one must be the penalty transaction itself.

BOLT anchors.
* BOLT 5 "Revoked Transaction Close Handling",
  `refs/bolts/05-onchain.md:510` (punish a revoked commitment),
  `:529` (spend the revoked `to_remote` output with the revocation key),
  `:547` (one transaction may resolve all revoked outputs).
* BOLT 3 `to_local` output and revocation branch,
  `refs/bolts/03-transactions.md:113`; `to_remote`,
  `refs/bolts/03-transactions.md:136`; `revocationpubkey`,
  `refs/bolts/03-transactions.md:799`.

rust-lightning anchors at pinned commit `fe49009`.
* `lightning/src/chain/channelmonitor.rs:5079`
  (`check_spend_counterparty_transaction`, revoked-commitment path).
* `lightning/src/chain/channelmonitor.rs:5104` (look up the revealed
  per-commitment secret), `:5110` (derive the revocation key and build the
  justice package).
* `lightning/src/ln/chan_utils.rs:2183` (`revokeable_output_index`) and
  `:2208` (`build_to_local_justice_tx`: one input, one output, value minus a
  fee).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`).

What is explicitly NOT modelled.
* Bitcoin script execution, ECDSA/revocation-signature checking, and the
  concrete secp256k1/shachain arithmetic.  `PenaltyL1Bridge.accepted` and
  `PenaltyL1Bridge.spends` are the explicit L1 interface.
* The precise script of the sweep output.  `controls` is an abstract
  ownership predicate supplied by the bridge, not a byte-level script proof.
* Fee bumping, package relay, pinning, watchtower liveness, and the
  economics of the penalty fee.  The fee is a parameter; the value bound is
  conditional on the usual non-negativity/feasibility hypotheses.
* HTLC-output penalties.  `PenaltyTx` has exactly the two main outputs.
-/

namespace LnLean.Proofs.PhaseC2

open LnLean
open LnLean.Channel
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## The L1 bridge for the penalty path -/

/-- The L1 facts needed by the penalty path, as an explicit interface.

`spends` is the L1 spend relation and `accepted` is L1 acceptance of a
transaction.  `spends_iff` identifies the bridge's spend relation with the
model's input-membership predicate `LnLean.Channel.Spends`, so the bridge
does not introduce a second, unrelated notion of spending.

Both L1 obligations are structure fields: `penaltyAccepted` connects
`penaltyValid` to L1 acceptance and `sweepControlled` connects the single
sweep output to honest ownership.  Neither is an axiom. -/
structure PenaltyL1Bridge where
  /-- L1 spend relation: transaction `tx` spends outpoint `o`. -/
  spends : Tx → OutPoint → Prop
  /-- L1 acceptance (script/witness acceptance plus on-chain inclusion). -/
  accepted : Tx → Prop
  /-- Abstract ownership predicate for an output script. -/
  controls : Script → Prop
  /-- The bridge's spend relation is the model's input-membership relation. -/
  spends_iff : ∀ (tx : Tx) (o : OutPoint), spends tx o ↔ Spends tx o
  /-- L1 no-double-spend for *distinct* transactions. -/
  noDoubleSpend : ∀ (t u : Tx) (o : OutPoint), t ≠ u →
    spends t o → spends u o → accepted t → ¬ accepted u
  /-- **L1 acceptance obligation** (a field, not an axiom): a model-valid
  penalty transaction is accepted by L1. -/
  penaltyAccepted : ∀ (scheme : RevocationScheme) (c : RevokedCommitment)
    (p : PenaltyTx) (w : PenaltyWitness) (confirm : Height) (window : Blocks),
    penaltyValid scheme c p w confirm window → accepted p.toTx
  /-- **Sweep ownership obligation**: the single output of a valid penalty is
  controlled by the honest party. -/
  sweepControlled : ∀ (scheme : RevocationScheme) (c : RevokedCommitment)
    (p : PenaltyTx) (w : PenaltyWitness) (confirm : Height) (window : Blocks),
    penaltyValid scheme c p w confirm window → controls p.sweep.scriptPubKey

/-! ## Spending both contested outputs -/

/-- Under the bridge, a transaction that spends both named old outputs
spends the old `to_local` outpoint. -/
theorem penaltyBridge_spends_toLocal (bridge : PenaltyL1Bridge)
    {c : RevokedCommitment} {p : PenaltyTx} (h : penaltySpendsBoth c p) :
    bridge.spends p.toTx c.toLocal :=
  (bridge.spends_iff p.toTx c.toLocal).2 (penalty_spends_toLocal h)

/-- Under the bridge, a transaction that spends both named old outputs
spends the old `to_remote` outpoint. -/
theorem penaltyBridge_spends_toRemote (bridge : PenaltyL1Bridge)
    {c : RevokedCommitment} {p : PenaltyTx} (h : penaltySpendsBoth c p) :
    bridge.spends p.toTx c.toRemote :=
  (bridge.spends_iff p.toTx c.toRemote).2 (penalty_spends_toRemote h)

/-- **Both contested outputs are spent.**  A valid penalty transaction is an
L1 spend of both old main outputs. -/
theorem penaltyBridge_valid_spends_both (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window) :
    bridge.spends p.toTx c.toLocal ∧ bridge.spends p.toTx c.toRemote :=
  ⟨penaltyBridge_spends_toLocal bridge (penaltyValid_spends hv),
   penaltyBridge_spends_toRemote bridge (penaltyValid_spends hv)⟩

/-- The penalty transaction has exactly one output, the sweep output. -/
theorem penaltyBridge_single_output (p : PenaltyTx) :
    p.toTx.vout = [p.sweep] := rfl

/-- The single sweep output is controlled by the honest party. -/
theorem penaltyBridge_sweep_controlled (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window) :
    bridge.controls p.sweep.scriptPubKey :=
  bridge.sweepControlled scheme c p w confirm window hv

/-- The bridge accepts a model-valid penalty transaction.  This is the
projection of the structure field, made a named theorem for composition. -/
theorem penaltyBridge_accepted (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window) :
    bridge.accepted p.toTx :=
  bridge.penaltyAccepted scheme c p w confirm window hv

/-! ## The value bound -/

/-- The sweep output value is the sum of both contested values minus the
penalty fee.  This is the value equation inherited from `penaltyValid`. -/
theorem penaltyBridge_sweep_value
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window) :
    p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee :=
  penaltyValid_sweep hv

/-- A non-negative fee keeps the sweep value at or below the sum of the two
contested values. -/
theorem penaltyBridge_sweep_le_total
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window)
    (hfee : 0 ≤ c.penaltyFee) :
    p.sweep.value ≤ c.toLocalValue + c.toRemoteValue := by
  rw [penaltyBridge_sweep_value hv]
  exact Int.sub_le_self _ hfee

/-- If the fee does not exceed the two contested values, the sweep value is
non-negative. -/
theorem penaltyBridge_sweep_nonneg
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window)
    (_hfee : 0 ≤ c.penaltyFee)
    (hfee_total : c.penaltyFee ≤ c.toLocalValue + c.toRemoteValue) :
    0 ≤ p.sweep.value := by
  rw [penaltyBridge_sweep_value hv]
  exact Int.sub_nonneg_of_le hfee_total

/-- **Value-bound composition.**  For a valid penalty with a feasible fee,
the single honest output is between zero and the total contested value. -/
theorem penaltyBridge_value_bound
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window)
    (hfee : 0 ≤ c.penaltyFee)
    (hfee_total : c.penaltyFee ≤ c.toLocalValue + c.toRemoteValue) :
    0 ≤ p.sweep.value ∧
      p.sweep.value ≤ c.toLocalValue + c.toRemoteValue :=
  ⟨penaltyBridge_sweep_nonneg hv hfee hfee_total,
   penaltyBridge_sweep_le_total hv hfee⟩

/-! ## Exclusive-spend composition -/

/-- A distinct accepted transaction cannot spend the old `to_local`
outpoint once the penalty transaction is accepted. -/
theorem penaltyBridge_excludes_distinct_toLocal (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks} {b : Tx}
    (hv : penaltyValid scheme c p w confirm window)
    (hspend : Spends b c.toLocal) (hne : b ≠ p.toTx) :
    ¬ bridge.accepted b := by
  intro hbacc
  exact (bridge.noDoubleSpend b p.toTx c.toLocal hne
    ((bridge.spends_iff b c.toLocal).2 hspend)
    (penaltyBridge_spends_toLocal bridge (penaltyValid_spends hv))
    hbacc)
    (penaltyBridge_accepted bridge hv)

/-- A distinct accepted transaction cannot spend the old `to_remote`
outpoint once the penalty transaction is accepted. -/
theorem penaltyBridge_excludes_distinct_toRemote (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks} {b : Tx}
    (hv : penaltyValid scheme c p w confirm window)
    (hspend : Spends b c.toRemote) (hne : b ≠ p.toTx) :
    ¬ bridge.accepted b := by
  intro hbacc
  exact (bridge.noDoubleSpend b p.toTx c.toRemote hne
    ((bridge.spends_iff b c.toRemote).2 hspend)
    (penaltyBridge_spends_toRemote bridge (penaltyValid_spends hv))
    hbacc)
    (penaltyBridge_accepted bridge hv)

/-- **Exclusive-spend composition.**  Any accepted transaction distinct from
the penalty transaction cannot spend either contested output. -/
theorem penaltyBridge_excludes_distinct_breacher (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks} {b : Tx}
    (hv : penaltyValid scheme c p w confirm window)
    (hb : BreacherSpend c b) (hne : b ≠ p.toTx) :
    ¬ bridge.accepted b := by
  rcases hb with hspend | hspend
  · exact penaltyBridge_excludes_distinct_toLocal bridge hv hspend hne
  · exact penaltyBridge_excludes_distinct_toRemote bridge hv hspend hne

/-- The strongest unconditional form: an accepted breacher spend must be the
penalty transaction itself. -/
theorem penaltyBridge_accepted_breacher_eq_penalty (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks} {b : Tx}
    (hv : penaltyValid scheme c p w confirm window)
    (hb : BreacherSpend c b) (hacc : bridge.accepted b) :
    b = p.toTx := by
  apply Classical.byContradiction
  intro hne
  exact penaltyBridge_excludes_distinct_breacher bridge hv hb hne hacc

/-- No accepted transaction can coexist with an accepted penalty while also
spending a contested output, unless it is the penalty transaction itself. -/
theorem penaltyBridge_no_accepted_coexistence (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks} {b : Tx}
    (hv : penaltyValid scheme c p w confirm window)
    (hb : BreacherSpend c b) (hne : b ≠ p.toTx) :
    ¬ (bridge.accepted p.toTx ∧ bridge.accepted b) := by
  intro hboth
  exact penaltyBridge_excludes_distinct_breacher bridge hv hb hne hboth.2

/-! ## Composition: breach, spends, single honest output, value -/

/-- **Main composition.**  A valid penalty after a breach spends both
contested outputs, has exactly one output controlled by the honest party,
and pays exactly the contested total minus the fee. -/
theorem penaltyBridge_breach_composition (bridge : PenaltyL1Bridge)
    {scheme : RevocationScheme} {c : RevokedCommitment} {p : PenaltyTx}
    {w : PenaltyWitness} {confirm : Height} {window : Blocks}
    (hv : penaltyValid scheme c p w confirm window) :
    breachDetected c ∧
      bridge.spends p.toTx c.toLocal ∧
      bridge.spends p.toTx c.toRemote ∧
      p.toTx.vout = [p.sweep] ∧
      bridge.controls p.sweep.scriptPubKey ∧
      p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee :=
  ⟨penaltyValid_breach hv,
   penaltyBridge_spends_toLocal bridge (penaltyValid_spends hv),
   penaltyBridge_spends_toRemote bridge (penaltyValid_spends hv),
   rfl,
   penaltyBridge_sweep_controlled bridge hv,
   penaltyBridge_sweep_value hv⟩

/-- The obligation interface of `penaltyObligation_punishable` composes with
the bridge: any breach satisfying the listed penalty premises is punishable. -/
theorem penaltyBridge_punishable_of_premises
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks)
    (hbreach : breachDetected c)
    (hkey : deriveRevocationPubkey scheme w.revocationBase
        (scheme.pointOf w.secret) =
      scheme.derivePrivkey w.revocationBase w.secret)
    (hspend : penaltySpendsBoth c p)
    (hsweep : p.sweep.value =
      c.toLocalValue + c.toRemoteValue - c.penaltyFee)
    (htimely : timelyL1Confirmation c.breachHeight confirm window) :
    punishable scheme c p w confirm window :=
  penaltyObligation_punishable scheme c p w confirm window
    hbreach hkey hspend hsweep htimely

/-! ## Compatibility with the source bridge, and the discovered gap -/

/-- Compatibility with the source theorem `punished_not_breacher_spendable`:
under an `L1ScriptBridge`, a confirmed valid penalty excludes a confirmed
breacher spend.  This is the phase-C statement, reused unchanged. -/
theorem penaltyBridge_source_punished_not_breacher_spendable
    (bridge : L1ScriptBridge) (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) (b : Tx)
    (hv : penaltyValid scheme c p w confirm window)
    (hb : BreacherSpend c b) (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  punished_not_breacher_spendable bridge scheme c p w confirm window b
    hv hb hconf

/-- **Discovered gap in the source bridge.**  `L1ScriptBridge.noDoubleSpend`
quantifies over all pairs `t`, `u`, including `t = u`.  A transaction spends
its own inputs, so any confirmed transaction contradicts the field: the
source bridge can accept no transaction at all.  The corrected
`PenaltyL1Bridge.noDoubleSpend` above adds the necessary distinctness
hypothesis. -/
theorem l1ScriptBridge_no_confirmed_spend (bridge : L1ScriptBridge)
    (tx : Tx) (o : OutPoint) (hspend : Spends tx o) :
    ¬ bridge.confirms tx := by
  intro hconf
  exact bridge.noDoubleSpend tx tx o hspend hspend hconf hconf

end LnLean.Proofs.PhaseC2
