import LnLean.Channel.Penalty
import LnLean.Channel.Revocation
import LnLean.Bitcoin.Seam

/-!
# LnLean.Proofs.Channel.PenaltyProps

English claim.  A valid penalty transaction for a revoked commitment
`penaltyValid scheme c p w confirm window`

1. spends both old main outputs, `c.toLocal` and `c.toRemote`, and has exactly
   one sweep output, `p.sweep`;
2. pays `c.toLocalValue + c.toRemoteValue - c.penaltyFee`, hence a
   non-negative fee leaves a non-negative sweep value whenever the fee does
   not exceed the two old outputs;
3. confirms only while the modelled punishment window is open, i.e. exactly
   when `c.breachHeight ≤ confirm ∧ confirm < c.breachHeight + window`;
4. cannot coexist with a confirmed breacher spend of either old output under
   the named L1 no-double-spend bridge;
5. is independent of the honest party's *current* commitment keys.  The
   penalty witness contains only the revealed per-commitment secret and the
   punisher's revocation basepoint, both belonging to the old commitment.

The sixth intended claim, "`penaltyValid` implies that `w.secret` is the
per-commitment secret of the breached commitment", is **not** a consequence
of the raw `penaltyValid` definition: `RevokedCommitment` carries no target
revocation key and no secret index, and the key conjunct of `penaltyValid` is
exactly `RevocationScheme.consistent`, which holds for every secret.  This
module therefore states the corrected property `penaltyValidBindsSecret`: it
adds the on-chain binding between the old output's target revocation key and
the shachain secret for `c.number`, and proves secret equality from that
binding plus injectivity of revocation-key derivation on secrets.  The gap is
recorded in `agents/reports/B15.md`.

BOLT anchors.  BOLT 5 "Revoked Transaction Close Handling",
`refs/bolts/05-onchain.md:510-559`; penalty transaction weights,
`refs/bolts/05-onchain.md:582`.  BOLT 3 `to_local` output and its immediate
revocation branch, `refs/bolts/03-transactions.md:113-134`; `to_remote`
output, `refs/bolts/03-transactions.md:136-144`; `revocationpubkey`
derivation, `refs/bolts/03-transactions.md:799-826`.

rust-lightning anchors at pinned commit `fe49009`.
* `lightning/src/ln/chan_utils.rs:537` (`derive_private_revocation_key`: the
  punisher derives the old output's key from the revealed commitment secret
  and its own revocation base secret).
* `lightning/src/ln/chan_utils.rs:687` (`get_revokeable_redeemscript`: the
  `to_local` script with the immediate revocation branch and the CSV branch).
* `lightning/src/ln/chan_utils.rs:2183` (`revokeable_output_index`) and
  `:2208` (`build_to_local_justice_tx`: one input, one output, value minus a
  fee).
* `lightning/src/chain/channelmonitor.rs:2424` (`sign_to_local_justice_tx`:
  signing requires the revocation secret for the *provided* commitment
  number, not the current commitment key).
* `lightning/src/chain/channelmonitor.rs:3102` (detecting that the
  counterparty broadcast a revoked state) and `:997`
  (`CounterpartyRevokedOutputClaimable`).

What is NOT modelled.  Bitcoin script execution, signature/ECDSA checking,
the exact `OP_CSV`/`OP_CLTV` byte semantics, and the concrete shachain /
secp256k1 arithmetic.  The punishment window is a parameter `window`, not the
`to_self_delay` read from the old commitment script; linking the two is left
to the script-semantics layer.  HTLC outputs, fee bumping, package relay,
watchtower liveness and the economics of the penalty fee are out of scope.
-/

namespace LnLean.Proofs.Channel

open LnLean
open LnLean.Channel
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## The punishment window -/

/-- The breacher's punishment window has closed at `confirm`.  This is the
negation of the `confirm < c.breachHeight + window` upper bound in
`timelyL1Confirmation`.  In BOLT 3 the analogous deadline is the old
`to_local` output's `to_self_delay`; here `window` is the model parameter. -/
def penaltyWindowClosed (c : RevokedCommitment) (window : Blocks)
    (confirm : Height) : Prop :=
  c.breachHeight + window ≤ confirm

/-- The open punishment window, written as an explicit interval. -/
def penaltyWindowOpen (c : RevokedCommitment) (window : Blocks)
    (confirm : Height) : Prop :=
  c.breachHeight ≤ confirm ∧ confirm < c.breachHeight + window

/-- The interval predicate is exactly the model's `timelyL1Confirmation`. -/
theorem penaltyWindowOpen_iff_timely (c : RevokedCommitment) (window : Blocks)
    (confirm : Height) :
    penaltyWindowOpen c window confirm ↔
      timelyL1Confirmation c.breachHeight confirm window :=
  Iff.rfl

/-! ## Structural facts about the constructed L1 transaction -/

/-- The penalty transaction has exactly two inputs: one per old main output. -/
theorem penaltyTx_vin_length (p : PenaltyTx) : p.toTx.vin.length = 2 := rfl

/-- The penalty transaction has exactly one output, the sweep output. -/
theorem penaltyTx_vout_eq_sweep (p : PenaltyTx) : p.toTx.vout = [p.sweep] := rfl

/-- The single output count, as a separately named checked fact. -/
theorem penaltyTx_vout_length (p : PenaltyTx) : p.toTx.vout.length = 1 := by
  simp [PenaltyTx.toTx]

/-- A valid penalty spends the old `to_local` output. -/
theorem penaltyValid_spends_toLocal {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    Spends p.toTx c.toLocal :=
  penalty_spends_toLocal (penaltyValid_spends h)

/-- A valid penalty spends the old `to_remote` output. -/
theorem penaltyValid_spends_toRemote {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    Spends p.toTx c.toRemote :=
  penalty_spends_toRemote (penaltyValid_spends h)

/-- **Both old outputs and one sweep output.**  The penalty transaction
spends `c.toLocal` and `c.toRemote`, and its only output is `p.sweep`.
BOLT 5 allows a single penalty transaction to resolve all revoked outputs
(`refs/bolts/05-onchain.md:545-558`). -/
theorem penaltyValid_spends_both_and_sweeps_one {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    Spends p.toTx c.toLocal ∧ Spends p.toTx c.toRemote ∧
      p.toTx.vout = [p.sweep] :=
  ⟨penaltyValid_spends_toLocal h, penaltyValid_spends_toRemote h, rfl⟩

/-! ## Sweep value and fee -/

/-- The sweep output is the sum of the two old outputs minus the penalty fee.
This is the value equation stored in `penaltyValid`. -/
theorem penaltyValid_sweep_eq_total_sub_fee {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee :=
  penaltyValid_sweep h

/-- Equivalently, the sweep value plus the fee is exactly the swept input
value.  This is the no-value-creation form of the previous equation. -/
theorem penaltyValid_sweep_add_fee {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    p.sweep.value + c.penaltyFee = c.toLocalValue + c.toRemoteValue := by
  rw [penaltyValid_sweep h]
  exact Int.sub_add_cancel _ _

/-- A non-negative penalty fee never increases the sweep value above the
sum of the two old outputs. -/
theorem penaltyValid_sweep_le_total {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window)
    (hfee : 0 ≤ c.penaltyFee) :
    p.sweep.value ≤ c.toLocalValue + c.toRemoteValue := by
  rw [penaltyValid_sweep h]
  exact Int.sub_le_self _ hfee

/-- If the fee is non-negative and does not exceed the two old outputs, the
sweep output is non-negative.  `penaltyValid` itself does not require this;
it is the economic precondition for a usable penalty transaction. -/
theorem penaltyValid_sweep_nonneg {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window)
    (_hfee : 0 ≤ c.penaltyFee)
    (hfee_total : c.penaltyFee ≤ c.toLocalValue + c.toRemoteValue) :
    0 ≤ p.sweep.value := by
  rw [penaltyValid_sweep h]
  exact Int.sub_nonneg_of_le hfee_total

/-! ## Timeliness: the exact predicate -/

/-- A valid penalty confirms inside the open punishment window. -/
theorem penaltyValid_confirmation_window {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    c.breachHeight ≤ confirm ∧ confirm < c.breachHeight + window :=
  penaltyValid_timely h

/-- Once the punishment window has closed, a `penaltyValid` proof is
impossible.  This is the formal "only valid before the window closes"
statement. -/
theorem penaltyValid_before_window_closes {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (h : penaltyValid scheme c p w confirm window) :
    ¬ penaltyWindowClosed c window confirm := by
  intro hclosed
  rcases penaltyValid_timely h with ⟨_, hhi⟩
  unfold penaltyWindowClosed at hclosed
  exact Nat.not_le_of_lt hhi hclosed

/-- Contrapositive form with the closed predicate as the hypothesis. -/
theorem not_penaltyValid_of_window_closed {scheme : RevocationScheme}
    {c : RevokedCommitment} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (hclosed : penaltyWindowClosed c window confirm) :
    ¬ penaltyValid scheme c p w confirm window := by
  intro hvalid
  exact penaltyValid_before_window_closes hvalid hclosed

/-! ## No double spend by the breacher -/

/-- Under the named L1 no-double-spend bridge, a valid penalty transaction
that is confirmed prevents any confirmed transaction from spending either
old output.  The breacher can therefore not also spend a punished output. -/
theorem penaltyValid_no_breacher_spend (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hvalid : penaltyValid scheme c p w confirm window)
    (hbreach : BreacherSpend c b)
    (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  punished_not_breacher_spendable bridge scheme c p w confirm window b
    hvalid hbreach hconf

/-- The `to_local` half of the no-double-spend result, stated separately. -/
theorem penaltyValid_blocks_toLocal_spend (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hvalid : penaltyValid scheme c p w confirm window)
    (hspend : Spends b c.toLocal)
    (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  bridge.noDoubleSpend p.toTx b c.toLocal
    (penaltyValid_spends_toLocal hvalid) hspend hconf

/-- The `to_remote` half of the no-double-spend result, stated separately. -/
theorem penaltyValid_blocks_toRemote_spend (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hvalid : penaltyValid scheme c p w confirm window)
    (hspend : Spends b c.toRemote)
    (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  bridge.noDoubleSpend p.toTx b c.toRemote
    (penaltyValid_spends_toRemote hvalid) hspend hconf

/-! ## Independence from the honest party's current commitment keys -/

/-- An abstraction of the honest party's *current* commitment keys.  None of
these values occurs in `PenaltyWitness`, `RevokedCommitment`, or
`penaltyValid`.  They are introduced only to state independence explicitly. -/
structure CurrentCommitmentKeys where
  paymentBase : PubKey
  delayedPaymentBase : PubKey
  revocationBase : PubKey
deriving Repr

/-- `penaltyValid` evaluated in a context carrying the honest party's current
keys.  The context is deliberately ignored. -/
def penaltyValidUnderKeys (_keys : CurrentCommitmentKeys)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) : Prop :=
  penaltyValid scheme c p w confirm window

/-- **Current-key independence.**  Penalty validity is the same for any two
choices of the honest party's current commitment keys. -/
theorem penaltyValid_current_key_independent
    (keys keys' : CurrentCommitmentKeys) (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) :
    penaltyValidUnderKeys keys scheme c p w confirm window ↔
      penaltyValidUnderKeys keys' scheme c p w confirm window :=
  Iff.rfl

/-- Unfolding form: the key context does not add a hypothesis to
`penaltyValid`. -/
theorem penaltyValid_ignores_current_keys
    (keys : CurrentCommitmentKeys) (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) :
    penaltyValidUnderKeys keys scheme c p w confirm window ↔
      penaltyValid scheme c p w confirm window :=
  Iff.rfl

/-! ## The revealed secret is the breached commitment's secret -/

/-- The revocation key that the old commitment's outputs are locked to,
computed from the shachain secret belonging to `c.number`. -/
def commitmentRevocationKey (scheme : RevocationScheme) (sh : Shachain)
    (c : RevokedCommitment) (base : PubKey) : RevocationKey :=
  revocationPubkeyOfSecret scheme base (revocationSecret sh c.number)

/-- The corrected, binding form of penalty validity.  In addition to
`penaltyValid`, it records that the old output really is locked to the
revocation key of the secret at `c.number` and that the witness secret opens
that same key.  This is the property the raw model cannot express because
`RevokedCommitment` does not store the target key. -/
def penaltyValidBindsSecret (scheme : RevocationScheme) (sh : Shachain)
    (c : RevokedCommitment) (base : PubKey) (target : RevocationKey)
    (p : PenaltyTx) (w : PenaltyWitness) (confirm : Height)
    (window : Blocks) : Prop :=
  penaltyValid scheme c p w confirm window ∧
    target = commitmentRevocationKey scheme sh c base ∧
    target = revocationPubkeyOfSecret scheme base w.secret

/-- **Secret binding theorem.**  If revocation-key derivation is injective on
secrets (the cryptographic premise that two distinct per-commitment secrets
cannot open the same old output) and the witness secret opens the old
commitment's target key, then the revealed secret is exactly the shachain
secret of the breached commitment number. -/
theorem penaltyValidBindsSecret_secret_eq {scheme : RevocationScheme}
    {sh : Shachain} {c : RevokedCommitment} {base : PubKey}
    {target : RevocationKey} {p : PenaltyTx} {w : PenaltyWitness}
    {confirm : Height} {window : Blocks}
    (hkey_inj : ∀ {s t : PerCommitmentSecret},
      revocationPubkeyOfSecret scheme base s =
        revocationPubkeyOfSecret scheme base t → s = t)
    (h : penaltyValidBindsSecret scheme sh c base target p w confirm window) :
    w.secret = revocationSecret sh c.number := by
  rcases h with ⟨_, htarget, hw⟩
  unfold commitmentRevocationKey at htarget
  exact hkey_inj (hw.symm.trans htarget)

/-- A breach of a commitment inside the BOLT 3 range still has a valid
shachain index. -/
theorem breach_number_le_max {c : RevokedCommitment}
    (hbreach : breachDetected c)
    (hcurrent : c.currentNumber ≤ MAX_COMMITMENT_NUMBER) :
    c.number ≤ MAX_COMMITMENT_NUMBER :=
  Nat.le_trans (Nat.le_of_lt hbreach) hcurrent

/-- Distinct breached commitments in the BOLT 3 range have distinct
per-commitment secrets.  This rules out reusing one revealed secret to
punish two different old commitment numbers. -/
theorem revocationSecret_breach_injective (sh : Shachain)
    {c d : RevokedCommitment}
    (hc : breachDetected c) (hd : breachDetected d)
    (hcurc : c.currentNumber ≤ MAX_COMMITMENT_NUMBER)
    (hcurd : d.currentNumber ≤ MAX_COMMITMENT_NUMBER)
    (hsecret : revocationSecret sh c.number = revocationSecret sh d.number) :
    c.number = d.number :=
  revocationSecret_injective sh
    (breach_number_le_max hc hcurc) (breach_number_le_max hd hcurd) hsecret

end LnLean.Proofs.Channel
