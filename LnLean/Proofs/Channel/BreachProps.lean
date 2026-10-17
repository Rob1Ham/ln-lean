import LnLean.Channel.Penalty
import LnLean.Channel.State

/-!
# LnLean.Proofs.Channel.BreachProps

English claim.  This module proves the breach/punishment laws of
`LnLean.Channel.Penalty` against the channel counters of
`LnLean.Channel.State`:

1. `breachDetected` fires exactly when the confirmed commitment is strictly
   older than the channel's current commitment, i.e. exactly when its
   per-commitment secret is in the revocation store (`BreachConfirmed`).
2. A commitment that equals the current commitment number is not a breach and
   is not punishable by the penalty path.
3. Once a penalty transaction is confirmed, the L1 no-double-spend bridge
   makes both old main outputs unavailable to the breacher.
4. The penalty sweep is worth the two breached main outputs minus the penalty
   fee, hence at least the breached `to_local` value minus the fee when the
   `to_remote` value is non-negative.
5. No penalty can confirm "timely" at or after the deadline
   `breachHeight + window`; a late breach therefore needs an explicit
   watchtower/online-observation hypothesis, which this module states as an
   interface rather than assuming.
6. The two-input `PenaltyTx` cannot itself spend a third (HTLC) output; the
   full HTLC-sweeping statement is left as a named, statement-only obligation.

BOLT sections and anchors (pinned BOLT commit, `refs/bolts`).
* BOLT 5 §Revoked Transaction Close Handling:
  `refs/bolts/05-onchain.md:510` (a previous commitment besides the most
  current one may be punished with the revocation key),
  `:529` (spend the remote main output with the revocation private key),
  `:547` (one transaction may resolve all revoked outputs),
  `:552` (a `security_delay` before expiry, node policy),
  `:582` (penalty transaction weight).
* BOLT 2 `revoke_and_ack` (revealing the per-commitment secret):
  `refs/bolts/02-peer-protocol.md:3206`.
* BOLT 3 `to_local` revocation branch: `refs/bolts/03-transactions.md:113`;
  `to_remote`: `:136`; `revocationpubkey`: `:799`; per-commitment secret
  range and generation: `:828`; compact 49-slot storage: `:860`.

rust-lightning anchors at commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/chain/channelmonitor.rs:5079`
  (`check_spend_counterparty_transaction`, the revoked-commitment path).
* `lightning/src/chain/channelmonitor.rs:5100` (recover the commitment
  number from the obscured sequence/locktime) and `:5101` (the
  `commitment_number >= get_min_seen_secret()` test that identifies a
  revoked commitment, dual to `breachDetected` in the increasing-counter
  encoding used here).
* `lightning/src/chain/channelmonitor.rs:5104` (look up the revealed
  per-commitment secret) and `:5107`/`:5110` (derive the revocation key and
  the revokeable script, then build the justice package).
* `lightning/src/chain/channelmonitor.rs:5021` (`sign_to_local_justice_tx`
  fails unless the monitor holds the secret for that commitment number) and
  `:3583` (`provide_secret` inserts the revealed secret).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`, used by the punisher).

What is explicitly NOT modelled.
* Bitcoin script execution and signature verification.  The L1 consequence
  is the named `L1ScriptBridge.noDoubleSpend` hypothesis; a valid revocation
  signature is never actually checked.
* Penalty fees, fee bumping, package relay, pinning, and the BOLT 5
  `security_delay` policy: `penaltyFee` is a parameter and economic viability
  is not claimed.
* Watchtower liveness.  `Watchtower` is an interface; `live` is a `Prop`,
  not a proved fact, and no theorem derives a report from liveness.
* HTLC-output penalties.  `PenaltyTx` has exactly the two main outputs; the
  generalisation is `PenaltyHtlcCoverage` (statement only).
* Concrete shachain/SHA-256/curve arithmetic: `Shachain` and
  `RevocationScheme` are parameters (see `Channel.Revocation`).
* Chain reorgs, non-atomic revocation edge cases, and the counterparty-vs-
  holder commitment orientation.  `RevokedCommitment` is a single
  broadcaster's commitment in the local view.

Build note.  `LnLean.Channel.HTLC` and `LnLean.Channel.State` cannot be
imported together: both declare `LnLean.Channel.HTLC` (`Channel/HTLC.lean:76`
and `Channel/Types.lean:142`), so the environment merge fails with
"environment already contains 'LnLean.Channel.HTLC.direction'".  This module
therefore imports `Channel.State` (which transitively provides
`Channel.Types`, including its `HTLC` record) and not `Channel.HTLC`.  This
is an integration item for the wave-A owner; no workaround is attempted here.
-/

namespace LnLean.Channel

open LnLean
open LnLean.Bitcoin

set_option autoImplicit false

/-! ## Definitions tying the penalty model to secrets, stores, and observers -/

/-- The honest party holds the per-commitment secret of the published
commitment: the decoded witness secret is exactly the shachain value for the
commitment number.  BOLT 3: `per_commitment_secret` is revealed by
`revoke_and_ack` (`refs/bolts/02-peer-protocol.md:3206`). -/
def HoldsRevocationSecret (sh : Shachain) (c : RevokedCommitment)
    (w : PenaltyWitness) : Prop :=
  w.secret = revocationSecret sh c.number

/-- A confirmed commitment is a breach when it is older than the current one
and its secret is in the revocation store.  The two conjuncts are the
number test and the storage test used by LDK at
`lightning/src/chain/channelmonitor.rs:5101`. -/
def BreachConfirmed (st : RevocationStore) (c : RevokedCommitment) : Prop :=
  breachDetected c ∧ isRevoked st c.number

/-- The honest notion of punishability: the core penalty conditions *plus*
possession of the commitment's own secret.  `punishable` alone cannot express
the latter because `RevocationScheme.consistent` is total (see the module
report); this definition makes the secret-binding premise explicit. -/
def HonestPunishable (sh : Shachain) (c : RevokedCommitment)
    (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) : Prop :=
  breachDetected c ∧
  HoldsRevocationSecret sh c w ∧
  penaltySpendsBoth c p ∧
  p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee ∧
  timelyL1Confirmation c.breachHeight confirm window

/-- The economic statement of the penalty transaction: it sweeps exactly the
two breached main outputs minus the fee, and a non-negative fee cannot make
the sweep exceed those outputs.  `BtcAmount` is `Int`, so the bracketed
implication is the only sign condition needed. -/
def PenaltyEconomicBound (c : RevokedCommitment) (p : PenaltyTx) : Prop :=
  p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee ∧
  (0 ≤ c.penaltyFee → p.sweep.value ≤ c.toLocalValue + c.toRemoteValue)

/-- An optional external watchtower.  `reports c h` means the tower reports
the breach of `c` at height `h`; `reports_live` records that a report is only
possible while the tower is live.  Liveness itself is never proved. -/
structure Watchtower where
  /-- The tower is live (an unproved external hypothesis). -/
  live : Prop
  /-- The tower reports the breach of a commitment at a height. -/
  reports : RevokedCommitment → Height → Prop
  /-- A report can only come from a live tower. -/
  reports_live : ∀ (c : RevokedCommitment) (h : Height), reports c h → live

/-- Modelled discovery routes: the honest party is online at height `h`, or a
watchtower reports the breach at `h`.  The model does not track node
liveness, so `online` is an explicit parameter. -/
def Detectable (online : Height → Prop) (wt : Watchtower)
    (c : RevokedCommitment) (h : Height) : Prop :=
  online h ∨ wt.reports c h

/-- Boolean mirror of `HTLC.isPending`, used only to filter lists.  The
`Prop` version in `Channel.Types` is not directly a `List.filter` predicate. -/
def isPendingBool (h : HTLC) : Bool :=
  match h.state with
  | .offered => true
  | .received => true
  | .fulfilled => false
  | .failed => false
  | .removed => false

/-- The Boolean filter and the `Prop` predicate agree (checked by cases). -/
theorem isPendingBool_iff (h : HTLC) : isPendingBool h = true ↔ h.isPending := by
  rcases h with ⟨d, a, ph, cltv, st⟩
  cases st <;> simp [isPendingBool, HTLC.isPending]

/-- Value of the pending HTLC outputs that a complete penalty transaction
would additionally sweep.  The concrete per-HTLC value is supplied by the
caller (`HTLC.amountSat` is the natural choice). -/
def pendingHtlcValue (hs : List HTLC) (value : HTLC → Nat) : Int :=
  ((hs.filter isPendingBool).map (fun h => (value h : Int))).sum

/-- **Obligation LN-BREACH-013 (statement only).**  A complete penalty
transaction also sweeps every pending HTLC output of the revoked commitment.
`PenaltyTx` has exactly two inputs (`penaltyTx_toTx_vin`), so this module can
only state the extended equality, not prove it; proving it requires extending
`PenaltyTx` with HTLC outpoints and their per-output values.
-/
-- OBLIGATION: LN-BREACH-013 A complete penalty also sweeps pending HTLC outputs (statement only here).
def PenaltyHtlcCoverage (c : RevokedCommitment) (p : PenaltyTx)
    (hs : List HTLC) (value : HTLC → Nat) : Prop :=
  (∃ h ∈ hs, h.isPending) →
    p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee +
      pendingHtlcValue hs value

/-! ## Detection is exactly the revoked/current test -/

/-- **Obligation LN-BREACH-001.**  With the store's `minSeen` equal to the
channel's current commitment number, "confirmed and revoked" is equivalent to
`breachDetected`: the number test and the secret-store test agree. -/
-- OBLIGATION: LN-BREACH-001 With minSeen = currentNumber, a confirmed commitment is revoked iff breachDetected.
theorem breachConfirmed_iff_of_minSeen (st : RevocationStore)
    (c : RevokedCommitment) (hmin : st.minSeen = c.currentNumber) :
    BreachConfirmed st c ↔ breachDetected c := by
  constructor
  · intro h
    exact h.1
  · intro hb
    refine ⟨hb, ?_⟩
    unfold isRevoked
    rw [hmin]
    exact hb

/-- **Obligation LN-BREACH-002.**  A commitment at the current commitment
number is not a breach.  This is the "current commitment is not punishable"
side of the exactness claim. -/
-- OBLIGATION: LN-BREACH-002 A commitment at the current commitment number is not a breach.
theorem not_breach_of_eq_current (c : RevokedCommitment)
    (h : c.number = c.currentNumber) : ¬ breachDetected c := by
  unfold breachDetected
  omega

/-- **Obligation LN-BREACH-003.**  A current (non-revoked) commitment is not
punishable by the penalty path, because `punishable` contains
`breachDetected`. -/
-- OBLIGATION: LN-BREACH-003 A current commitment is not punishable by the penalty path.
theorem current_commitment_not_punishable (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks)
    (h : c.number = c.currentNumber) :
    ¬ punishable scheme c p w confirm window := by
  intro hp
  exact not_breach_of_eq_current c h hp.1

/-- **Obligation LN-BREACH-004.**  Along any reachable channel history, a
commitment numbered below the *initial* local commitment counter and
confirmed while the channel is at a later counter is a breach.  This uses
`Reachable.localCommitmentNumber_le` from `Channel.State`. -/
-- OBLIGATION: LN-BREACH-004 Any reachable history preserves the breach test below its initial counter.
theorem confirmed_below_reachable_current_is_breach {a b : Channel}
    (hreach : Reachable a b) (c : RevokedCommitment)
    (hcur : c.currentNumber = b.localCommitmentNumber)
    (hbelow : c.number < a.localCommitmentNumber) :
    breachDetected c := by
  unfold breachDetected
  rw [hcur]
  exact Nat.lt_of_lt_of_le hbelow (Reachable.localCommitmentNumber_le hreach)

/-! ## Punishability: secret, spend, value, and time -/

/-- **Obligation LN-BREACH-005.**  In the abstract scheme the derived public
and private revocation keys agree for *every* secret (`RevocationScheme.consistent`),
so the key conjunct of `penaltyValid` is redundant.  A valid penalty is
therefore exactly: breach, both outputs spent, the sweep-value equation, and
a timely confirmation. -/
-- OBLIGATION: LN-BREACH-005 A valid penalty is breach, both-output spend, sweep value, and timely confirmation.
theorem penaltyValid_iff_core (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) :
    penaltyValid scheme c p w confirm window ↔
      breachDetected c ∧
      penaltySpendsBoth c p ∧
      p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee ∧
      timelyL1Confirmation c.breachHeight confirm window := by
  unfold penaltyValid
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro ⟨hb, hs, hv, ht⟩
    exact ⟨hb,
      deriveRevocationPubkey_consistent scheme w.revocationBase w.secret,
      hs, hv, ht⟩

/-- **Obligation LN-BREACH-006.**  `punishable` reduces to the same four core
conditions; the protocol-level wrapper adds nothing beyond `breachDetected`. -/
-- OBLIGATION: LN-BREACH-006 Punishable reduces to the four core penalty conditions.
theorem punishable_iff_core (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) :
    punishable scheme c p w confirm window ↔
      breachDetected c ∧
      penaltySpendsBoth c p ∧
      p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee ∧
      timelyL1Confirmation c.breachHeight confirm window := by
  constructor
  · intro hp
    have hcore := (penaltyValid_iff_core scheme c p w confirm window).1 hp.2
    exact ⟨hp.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2⟩
  · intro ⟨hb, hs, hv, ht⟩
    exact ⟨hb,
      (penaltyValid_iff_core scheme c p w confirm window).2 ⟨hb, hs, hv, ht⟩⟩

/-- **Obligation LN-BREACH-007.**  Corrected "punishable iff the honest party
holds the revocation secret and can confirm a penalty within the window":
`HonestPunishable` is equivalent to holding that commitment's secret together
with `punishable`.  The secret-possession conjunct cannot be dropped from the
left-hand side in this abstract model; see LN-BREACH-005 and the report. -/
-- OBLIGATION: LN-BREACH-007 Honest punishability is holding the commitment secret plus punishable.
theorem honestPunishable_iff (sh : Shachain) (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks) :
    HonestPunishable sh c p w confirm window ↔
      HoldsRevocationSecret sh c w ∧
      punishable scheme c p w confirm window := by
  constructor
  · intro h
    rcases h with ⟨hb, hsec, hs, hv, ht⟩
    exact ⟨hsec,
      (punishable_iff_core scheme c p w confirm window).2 ⟨hb, hs, hv, ht⟩⟩
  · intro ⟨hsec, hp⟩
    have hcore := (punishable_iff_core scheme c p w confirm window).1 hp
    exact ⟨hcore.1, hsec, hcore.2.1, hcore.2.2.1, hcore.2.2.2⟩

/-! ## The punished outputs are unavailable to the breacher -/

/-- **Obligation LN-BREACH-008.**  Once the penalty transaction confirms, the
breacher cannot also confirm a transaction spending the old `to_local`
output.  Relative to the named L1 no-double-spend bridge. -/
-- OBLIGATION: LN-BREACH-008 A confirmed penalty makes the old to_local output unavailable to the breacher.
theorem punished_toLocal_unavailable (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hv : penaltyValid scheme c p w confirm window)
    (hb : Spends b c.toLocal)
    (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  bridge.noDoubleSpend p.toTx b c.toLocal
    (penalty_spends_toLocal (penaltyValid_spends hv)) hb hconf

/-- **Obligation LN-BREACH-009.**  The same for the old `to_remote` output. -/
-- OBLIGATION: LN-BREACH-009 A confirmed penalty makes the old to_remote output unavailable to the breacher.
theorem punished_toRemote_unavailable (bridge : L1ScriptBridge)
    (scheme : RevocationScheme) (c : RevokedCommitment) (p : PenaltyTx)
    (w : PenaltyWitness) (confirm : Height) (window : Blocks) (b : Tx)
    (hv : penaltyValid scheme c p w confirm window)
    (hb : Spends b c.toRemote)
    (hconf : bridge.confirms p.toTx) :
    ¬ bridge.confirms b :=
  bridge.noDoubleSpend p.toTx b c.toRemote
    (penalty_spends_toRemote (penaltyValid_spends hv)) hb hconf

/-! ## The economic bound -/

/-- **Obligation LN-BREACH-010.**  If the old `to_remote` value is
non-negative, the sweep is at least the breached `to_local` value minus the
penalty fee.  This is the per-output lower bound; the fee is a parameter of
the model, not a fee-estimation result. -/
-- OBLIGATION: LN-BREACH-010 The sweep is at least the old to_local value minus the fee when to_remote is non-negative.
theorem sweep_ge_toLocal_sub_fee (c : RevokedCommitment) (p : PenaltyTx)
    (hsweep : p.sweep.value =
      c.toLocalValue + c.toRemoteValue - c.penaltyFee)
    (hremote : 0 ≤ c.toRemoteValue) :
    c.toLocalValue - c.penaltyFee ≤ p.sweep.value := by
  let L : Int := c.toLocalValue
  let R : Int := c.toRemoteValue
  let F : Int := c.penaltyFee
  let S : Int := p.sweep.value
  have hS : S = L + R - F := hsweep
  have hR : 0 ≤ R := hremote
  change L - F ≤ S
  omega

/-- **Obligation LN-BREACH-011.**  A valid penalty's sweep equals the two old
main outputs minus the fee, and a non-negative fee keeps it at or below the
total breached main-output value.  This is the `PenaltyEconomicBound`. -/
-- OBLIGATION: LN-BREACH-011 A valid penalty pays both old main outputs minus the fee, and no more when the fee is non-negative.
theorem penaltyEconomicBound_of_valid (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks)
    (hv : penaltyValid scheme c p w confirm window) :
    PenaltyEconomicBound c p := by
  refine ⟨penaltyValid_sweep hv, ?_⟩
  intro hfee
  let L : Int := c.toLocalValue
  let R : Int := c.toRemoteValue
  let F : Int := c.penaltyFee
  let S : Int := p.sweep.value
  have hS : S = L + R - F := penaltyValid_sweep hv
  have hF : 0 ≤ F := hfee
  change S ≤ L + R
  omega

/-! ## Timing and the watchtower boundary -/

/-- **Obligation LN-BREACH-012.**  The timely-confirmation predicate is
exactly the half-open interval `[breachHeight, breachHeight + window)`. -/
-- OBLIGATION: LN-BREACH-012 Timely confirmation is exactly the half-open window [breach, breach + window).
theorem timely_iff (c : RevokedCommitment) (confirm : Height)
    (window : Blocks) :
    timelyL1Confirmation c.breachHeight confirm window ↔
      c.breachHeight ≤ confirm ∧ confirm < c.breachHeight + window :=
  Iff.rfl

/-- **Obligation LN-BREACH-014.**  At or after the deadline no confirmation is
timely. -/
-- OBLIGATION: LN-BREACH-014 No confirmation at or after the deadline is timely.
theorem not_timely_at_deadline (c : RevokedCommitment) (confirm : Height)
    (window : Blocks) (h : c.breachHeight + window ≤ confirm) :
    ¬ timelyL1Confirmation c.breachHeight confirm window := by
  let B : Nat := c.breachHeight
  let W : Nat := window
  let C : Nat := confirm
  have hB : B + W ≤ C := h
  unfold timelyL1Confirmation
  change ¬ (B ≤ C ∧ C < B + W)
  omega

/-- **Obligation LN-BREACH-015.**  Consequently no penalty can be valid (and
no breach punishable) with a confirmation at or after the window closes. -/
-- OBLIGATION: LN-BREACH-015 No penalty is punishable with a confirmation after the revocation window.
theorem no_punishable_after_window (scheme : RevocationScheme)
    (c : RevokedCommitment) (p : PenaltyTx) (w : PenaltyWitness)
    (confirm : Height) (window : Blocks)
    (h : c.breachHeight + window ≤ confirm) :
    ¬ punishable scheme c p w confirm window := by
  intro hp
  exact not_timely_at_deadline c confirm window h (penaltyValid_timely hp.2)

/-- **Obligation LN-BREACH-016.**  A watchtower report implies the tower's
liveness.  This is the only direction the interface provides; the converse
(live tower reports) is deliberately not assumed. -/
-- OBLIGATION: LN-BREACH-016 A watchtower report implies the tower is live.
theorem watchtower_report_implies_live (wt : Watchtower)
    (c : RevokedCommitment) (h : Height) (hr : wt.reports c h) :
    wt.live :=
  wt.reports_live c h hr

/-- **Obligation LN-BREACH-017.**  If the honest party is not online at the
observation height, the only modelled route to detection is a watchtower
report, which in turn requires a live watchtower.  This is the precise,
conditional form of "a late breach needs an additional watchtower
assumption"; detection itself is not derivable from the model. -/
-- OBLIGATION: LN-BREACH-017 Offline late detection requires a live watchtower report.
theorem detected_after_deadline_requires_watchtower (online : Height → Prop)
    (wt : Watchtower) (c : RevokedCommitment) (h : Height)
    (hdet : Detectable online wt c h) (hno : ¬ online h) :
    wt.live := by
  rcases hdet with ho | hr
  · exact absurd ho hno
  · exact wt.reports_live c h hr

/-- **Obligation LN-BREACH-018.**  With the honest party offline and no
watchtower report, the model derives no detection at all.  This is the
negative form of LN-BREACH-017 and the reason the watchtower is an explicit
extra assumption. -/
-- OBLIGATION: LN-BREACH-018 With the party offline and no report, the model derives no detection.
theorem not_detected_without_observation_or_report (wt : Watchtower)
    (c : RevokedCommitment) (h : Height)
    (hno : ¬ wt.reports c h) :
    ¬ Detectable (fun _ => False) wt c h := by
  intro hd
  rcases hd with ho | hr
  · exact ho
  · exact hno hr

/-! ## The HTLC-output boundary -/

/-- **Obligation LN-BREACH-019.**  `PenaltyTx` has exactly two inputs, so it
cannot itself spend a third outpoint such as an HTLC output.  Any outpoint
different from both named inputs is not spent by `p.toTx`. -/
-- OBLIGATION: LN-BREACH-019 A two-input penalty transaction spends no third outpoint.
theorem penaltyTx_no_third_input (p : PenaltyTx) (o : OutPoint)
    (hL : o ≠ p.inputLocal) (hR : o ≠ p.inputRemote) :
    ¬ Spends p.toTx o := by
  intro hs
  rcases hs with ⟨i, hi, hprev⟩
  simp only [PenaltyTx.toTx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hL hprev.symm
  · exact hR hprev.symm

end LnLean.Channel
