import LnLean.Security.Invariants
import LnLean.Security.Model
import LnLean.Bitcoin.Laws
import LnLean.Channel.Laws
import LnLean.Routing.Laws
import LnLean.Proofs.Channel.BreachProps

/-!
# LnLean.Proofs.WaveE.E35 — the watchtower bridge for revoked-commitment punishment

## English claim (catalog `LN-SEC-006`)

A breach is punished if some party has the revocation secret and a timely L1
transaction, given a live watchtower.

## What is actually proved here

The claim decomposes into four model objects:

* a *breach*: a published commitment whose number is below the channel's
  current commitment number (`breachDetected`);
* a *party response*: a party that holds the per-commitment secret of the
  published commitment (`HoldsRevocationSecret`) and has a penalty
  transaction that spends both old main outputs, sweeps their value minus
  the penalty fee, and confirms inside the revocation window
  (`BreachResponse`);
* an *L1 effect*: the penalty transaction is confirmed, and therefore the
  breacher cannot confirm any transaction spending either old output
  (`L1ScriptBridge.noDoubleSpend`);
* a *detection route*: the honest party is online, or a live watchtower
  reports the breach (`Detectable`, `Watchtower.reports_live`).

`waveE_e35_watchtower_bridge` composes them: a watchtower that reports the
breach at the breach height is necessarily live, and together with a
`BreachResponse` the breach is punished on L1 and is `punishable` in the
sense of `LnLean.Channel.Penalty`.

## The precise gap

`Watchtower` (in `LnLean.Proofs.Channel.BreachProps`) has exactly two
behavioural fields, `live : Prop` and `reports : RevokedCommitment → Height →
Prop`, plus the one-way law `reports → live`.  It has **no** field saying
that a *live* tower reports, and **no** field saying that a reporting tower
holds the revocation secret or broadcasts a penalty transaction.  The model
therefore cannot derive punishment from `wt.live` alone.  The response is an
explicit parameter of every positive theorem below, and
`waveE_e35_live_watchtower_alone_does_not_punish` is a mechanized
counterexample to the unconditional reading: a live tower that never reports,
an offline honest party, and an L1 bridge that confirms nothing leave a
genuine breach undetected and unpunished.

## BOLT / LDK anchors

* BOLT 5 §Revoked Transaction Close Handling: a previous commitment besides
  the most current one may be punished with the revocation key; one
  transaction may resolve all revoked outputs (`refs/bolts/05-onchain.md:510`,
  `:529`, `:547`).
* BOLT 3 §Per-commitment Secret Requirements and `revocationpubkey`
  derivation (`refs/bolts/03-transactions.md:799`, `:828`).
* `lightning/src/chain/channelmonitor.rs:5079`
  (`check_spend_counterparty_transaction`, the revoked-commitment path),
  `:5101` (the `get_min_seen_secret` test), `:5104` (look up the revealed
  secret), `:5107`/`:5110` (derive the revocation key and build the justice
  package).

Nothing here executes Bitcoin script, implements the shachain, or proves
watchtower liveness; those remain explicit parameters/hypotheses, exactly as
in `LnLean.Channel.Penalty` and `LnLean.Proofs.Channel.BreachProps`.
-/

namespace LnLean.Proofs.WaveE.E35

open LnLean
open LnLean.Bitcoin
open LnLean.Channel

set_option autoImplicit false

/-! ## The response of a party that can punish

`BreachResponse` is the model-side reading of "some party has the revocation
secret and a timely L1 transaction".  It is data, not an axiom: an
instantiation must exhibit the witness, the transaction, the confirmation
height, and each premise.  The `holdsSecret` field is kept because
`punishable` alone cannot express secret possession (the abstract
`RevocationScheme.consistent` law is total; see LN-BREACH-005/007). -/

/-- A party's answer to a revoked-commitment close.  The party holds the
commitment's per-commitment secret and has a penalty transaction that spends
both old main outputs, sweeps their value minus the penalty fee, and confirms
inside the revocation window. -/
structure BreachResponse (sh : Shachain) (bridge : L1ScriptBridge)
    (c : RevokedCommitment) where
  /-- The per-commitment secret and the punisher's revocation basepoint. -/
  witness : PenaltyWitness
  /-- The penalty transaction built from the witness. -/
  tx : PenaltyTx
  /-- Height at which the penalty transaction confirms. -/
  confirm : Height
  /-- Length of the revocation window, in blocks. -/
  window : Blocks
  /-- The published commitment is old. -/
  breach : breachDetected c
  /-- The witness secret is the shachain secret of this commitment. -/
  holdsSecret : HoldsRevocationSecret sh c witness
  /-- The penalty spends both old main outputs. -/
  spends : penaltySpendsBoth c tx
  /-- The penalty sweeps both old main outputs minus the fee. -/
  sweep : tx.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee
  /-- The confirmation falls inside `[breachHeight, breachHeight + window)`. -/
  timely : timelyL1Confirmation c.breachHeight confirm window
  /-- The L1 bridge confirms the penalty transaction. -/
  confirmed : bridge.confirms tx.toTx

/-- The breach is punished on L1: an old commitment's two main outputs are
spent by a penalty transaction that confirms inside the revocation window.
This is the conclusion of the catalog claim; it says nothing about *who*
supplied the transaction. -/
def BreachPunished (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (p : PenaltyTx) (confirm : Height) (window : Blocks) : Prop :=
  breachDetected c ∧
    penaltySpendsBoth c p ∧
    bridge.confirms p.toTx ∧
    timelyL1Confirmation c.breachHeight confirm window

/-- The full L1 effect: the breach is punished and no transaction spending
either old output of the revoked commitment can confirm. -/
def PunishmentEffective (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (p : PenaltyTx) (confirm : Height) (window : Blocks) : Prop :=
  BreachPunished bridge c p confirm window ∧
    ∀ b : Tx, BreacherSpend c b → ¬ bridge.confirms b

/-! ## From a response to punishment -/

/-- A response punishes the breach: all four conjuncts of `BreachPunished`
are fields of `BreachResponse`. -/
theorem waveE_e35_punished_of_response (sh : Shachain) (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (r : BreachResponse sh bridge c) :
    BreachPunished bridge c r.tx r.confirm r.window :=
  ⟨r.breach, r.spends, r.confirmed, r.timely⟩

/-- A response is a valid `punishable` penalty in the sense of
`LnLean.Channel.Penalty`: the cryptographic key conjunct is discharged by
`RevocationScheme.consistent`, so only the four core conditions are needed. -/
theorem waveE_e35_response_punishable (scheme : RevocationScheme)
    (sh : Shachain) (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c) :
    punishable scheme c r.tx r.witness r.confirm r.window :=
  (punishable_iff_core scheme c r.tx r.witness r.confirm r.window).2
    ⟨r.breach, r.spends, r.sweep, r.timely⟩

/-- A response also satisfies the *honest* punishability predicate, which
records possession of the commitment's own secret. -/
theorem waveE_e35_response_honestly_punishable (sh : Shachain)
    (scheme : RevocationScheme) (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (r : BreachResponse sh bridge c) :
    HonestPunishable sh c r.tx r.witness r.confirm r.window :=
  (honestPunishable_iff sh scheme c r.tx r.witness r.confirm r.window).2
    ⟨r.holdsSecret, waveE_e35_response_punishable scheme sh bridge c r⟩

/-- Punishment is effective: once the penalty confirms, the L1
no-double-spend bridge rules out any breacher transaction spending either old
output.  This is the on-chain effect that makes the attack unprofitable, as
opposed to the mere existence of a penalty transaction. -/
theorem waveE_e35_punished_blocks_breacher (sh : Shachain)
    (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c) (b : Tx) (hb : BreacherSpend c b) :
    ¬ bridge.confirms b :=
  penaltyObligation_no_breacher_spend bridge c r.tx b r.spends hb r.confirmed

/-- The effective form of the bridge theorem: the response both confirms the
penalty and locks the breacher out of both old outputs. -/
theorem waveE_e35_response_effective (sh : Shachain) (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (r : BreachResponse sh bridge c) :
    PunishmentEffective bridge c r.tx r.confirm r.window :=
  ⟨waveE_e35_punished_of_response sh bridge c r,
   fun b hb => waveE_e35_punished_blocks_breacher sh bridge c r b hb⟩

/-- Liveness form: a response yields a finite height at which the breach is
punished.  The witness is the response's own confirmation height. -/
theorem waveE_e35_eventually_punished (sh : Shachain) (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (r : BreachResponse sh bridge c) :
    ∃ h : Height, c.breachHeight ≤ h ∧
      BreachPunished bridge c r.tx h r.window :=
  ⟨r.confirm, r.timely.1, r.breach, r.spends, r.confirmed, r.timely⟩

/-! ## The watchtower bridge -/

/-- **`LN-SEC-006` / `LnLean.Proofs.Liveness.watchtower_bridge`.**  If a
watchtower reports the breach at the breach height (hence is live, by
`Watchtower.reports_live`) and some party has a `BreachResponse`, then the
breach is punished on L1, is `punishable`, and the tower is live.

The report hypothesis is essential: `wt.live` alone does not imply
`wt.reports` in this model (see
`waveE_e35_live_watchtower_alone_does_not_punish`). -/
-- OBLIGATION: LN-WE-E35
theorem waveE_e35_watchtower_bridge (sh : Shachain)
    (scheme : RevocationScheme) (bridge : L1ScriptBridge) (wt : Watchtower)
    (c : RevokedCommitment) (r : BreachResponse sh bridge c)
    (hreport : wt.reports c c.breachHeight) :
    BreachPunished bridge c r.tx r.confirm r.window ∧
      punishable scheme c r.tx r.witness r.confirm r.window ∧
      wt.live :=
  ⟨waveE_e35_punished_of_response sh bridge c r,
   waveE_e35_response_punishable scheme sh bridge c r,
   wt.reports_live c c.breachHeight hreport⟩

/-- If the honest party is offline at the breach height, detection can only
come from a live watchtower.  This is the precise role of the watchtower in
the claim: it supplies detection when self-observation is unavailable. -/
theorem waveE_e35_offline_detection_requires_live_watchtower
    (online : Height → Prop) (wt : Watchtower) (c : RevokedCommitment)
    (h : Height) (hdet : Detectable online wt c h) (hoffline : ¬ online h) :
    wt.live :=
  detected_after_deadline_requires_watchtower online wt c h hdet hoffline

/-! ## Timing, value, and secret binding -/

/-- A punished breach confirms strictly before the revocation window closes. -/
theorem waveE_e35_punishment_within_window (sh : Shachain)
    (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c) :
    c.breachHeight ≤ r.confirm ∧ r.confirm < c.breachHeight + r.window :=
  r.timely

/-- No penalty is timely at or after the deadline: a late detection needs the
watchtower, and even then the response must already be inside the window. -/
theorem waveE_e35_punishment_deadline (sh : Shachain)
    (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c) {confirm : Height}
    (h : c.breachHeight + r.window ≤ confirm) :
    ¬ timelyL1Confirmation c.breachHeight confirm r.window :=
  not_timely_at_deadline c confirm r.window h

/-- The penalty pays at least the old `to_local` value minus the fee when the
old `to_remote` value is non-negative.  Economic viability of the fee itself
is not claimed (BOLT 5's fee policy is out of scope). -/
theorem waveE_e35_punishment_value_bound (sh : Shachain)
    (bridge : L1ScriptBridge) (c : RevokedCommitment)
    (r : BreachResponse sh bridge c) (hremote : 0 ≤ c.toRemoteValue) :
    c.toLocalValue - c.penaltyFee ≤ r.tx.sweep.value :=
  sweep_ge_toLocal_sub_fee c r.tx r.sweep hremote

/-- The revocation secret binds the commitment: the same shachain secret
cannot be the correct secret of two distinct commitment numbers in the BOLT 3
range.  This is the substantive content of "has the revocation secret"; it
uses the shachain's injectivity law, not the (total) revocation scheme. -/
theorem waveE_e35_secret_binds_commitment (sh : Shachain)
    {c c' : RevokedCommitment} {w : PenaltyWitness}
    (h : HoldsRevocationSecret sh c w) (h' : HoldsRevocationSecret sh c' w)
    (hc : c.number ≤ MAX_COMMITMENT_NUMBER)
    (hc' : c'.number ≤ MAX_COMMITMENT_NUMBER) :
    c.number = c'.number := by
  unfold HoldsRevocationSecret at h h'
  exact revocationSecret_injective sh hc hc' (h.symm.trans h')

/-- The same binding expressed against a revocation store: any two revoked
commitment numbers with the same secret are equal.  Both numbers are in the
BOLT 3 range by `isRevoked_index_bound`. -/
theorem waveE_e35_stored_secret_binds_commitment (sh : Shachain)
    (st : RevocationStore) {c c' : RevokedCommitment} {w : PenaltyWitness}
    (hr : isRevoked st c.number) (hr' : isRevoked st c'.number)
    (h : HoldsRevocationSecret sh c w) (h' : HoldsRevocationSecret sh c' w) :
    c.number = c'.number := by
  apply waveE_e35_secret_binds_commitment sh h h'
  · have hb := isRevoked_index_bound st hr
    unfold MAX_COMMITMENT_NUMBER COMMITMENT_SECRET_COUNT at *
    omega
  · have hb := isRevoked_index_bound st hr'
    unfold MAX_COMMITMENT_NUMBER COMMITMENT_SECRET_COUNT at *
    omega

/-- A punished commitment is necessarily an old commitment. -/
theorem waveE_e35_punished_commitment_is_old (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (p : PenaltyTx) (confirm : Height)
    (window : Blocks) (hp : BreachPunished bridge c p confirm window) :
    c.number < c.currentNumber :=
  hp.1

/-- No false positives: a commitment at the current commitment number is not
punished.  The penalty path only applies to revoked commitments. -/
theorem waveE_e35_current_commitment_not_punished (bridge : L1ScriptBridge)
    (c : RevokedCommitment) (p : PenaltyTx) (confirm : Height)
    (window : Blocks) (h : c.number = c.currentNumber) :
    ¬ BreachPunished bridge c p confirm window := by
  intro hp
  exact not_breach_of_eq_current c h hp.1

/-! ## Negative result: a live watchtower is not a reporting watchtower

The claim says "given a live watchtower".  The `Watchtower` interface only
provides `reports → live`, so a live tower may be modelled with an empty
`reports` relation.  The following concrete instances are legitimate model
values, and the theorem below shows that liveness alone implies neither
detection nor punishment. -/

/-- A watchtower that is live but never reports any breach. -/
def silentWatchtower : Watchtower where
  live := True
  reports := fun _ _ => False
  reports_live := by
    intro _ _ _
    trivial

/-- An L1 bridge under which no transaction ever confirms. -/
def silentBridge : L1ScriptBridge where
  confirms := fun _ => False
  noDoubleSpend := by
    intro _ _ _ _ _ _ hd
    exact hd

/-- A concrete genuine breach: commitment 0 published while the channel is at
commitment 1. -/
def sampleBreach : RevokedCommitment where
  number := 0
  currentNumber := 1
  toLocal := ⟨ByteArray.empty, 0⟩
  toRemote := ⟨ByteArray.empty, 1⟩
  toLocalValue := 100000
  toRemoteValue := 50000
  breachHeight := 800000
  penaltyFee := 1000

theorem waveE_e35_sampleBreach_detected : breachDetected sampleBreach := by
  unfold breachDetected sampleBreach
  decide

/-- The silent tower is live. -/
theorem waveE_e35_silent_watchtower_live : silentWatchtower.live :=
  trivial

/-- The silent tower never reports. -/
theorem waveE_e35_silent_watchtower_never_reports (c : RevokedCommitment)
    (h : Height) : ¬ silentWatchtower.reports c h :=
  fun hr => hr

/-- A live tower and an offline honest party yield no detection at all, for
any commitment and any height. -/
theorem waveE_e35_live_watchtower_need_not_detect (c : RevokedCommitment)
    (h : Height) :
    silentWatchtower.live ∧
      ¬ Detectable (fun _ : Height => False) silentWatchtower c h := by
  refine ⟨trivial, ?_⟩
  intro hd
  rcases hd with ho | hr
  · exact ho
  · exact hr

/-- Punishment requires a confirming L1 transaction: if the bridge does not
confirm the penalty, `BreachPunished` fails, whatever secret the party
holds. -/
theorem waveE_e35_no_punishment_without_confirmation
    (bridge : L1ScriptBridge) (c : RevokedCommitment) (p : PenaltyTx)
    (confirm : Height) (window : Blocks)
    (h : ¬ bridge.confirms p.toTx) :
    ¬ BreachPunished bridge c p confirm window := by
  intro hp
  exact h hp.2.2.1

/-- **Mechanized counterexample to the unconditional reading.**  A live
watchtower (`silentWatchtower`), an offline honest party, and an L1 bridge
that confirms nothing leave the genuine breach `sampleBreach` undetected at
every height and unpunished by every penalty transaction.  Hence the
catalog claim needs the report/response bridge supplied by
`waveE_e35_watchtower_bridge`, not merely `Watchtower.live`. -/
theorem waveE_e35_live_watchtower_alone_does_not_punish
    (p : PenaltyTx) (confirm : Height) (window : Blocks) :
    silentWatchtower.live ∧
      ¬ Detectable (fun _ : Height => False) silentWatchtower sampleBreach confirm ∧
      ¬ BreachPunished silentBridge sampleBreach p confirm window := by
  refine ⟨trivial, ?_, ?_⟩
  · exact (waveE_e35_live_watchtower_need_not_detect sampleBreach confirm).2
  · exact waveE_e35_no_punishment_without_confirmation silentBridge sampleBreach p
      confirm window (by simp [silentBridge])

/-- The non-L1 ingredients (an old commitment, a both-output penalty, a
timely height) do not by themselves make punishment effective: the penalty
transaction must actually confirm.  This isolates the second missing field,
`reports → confirmed penalty`, from the first, `live → reports`. -/
theorem waveE_e35_effective_requires_confirmation
    (bridge : L1ScriptBridge) (c : RevokedCommitment) (p : PenaltyTx)
    (confirm : Height) (window : Blocks)
    (_hbreach : breachDetected c) (_hspends : penaltySpendsBoth c p)
    (_htimely : timelyL1Confirmation c.breachHeight confirm window)
    (h : ¬ bridge.confirms p.toTx) :
    ¬ PunishmentEffective bridge c p confirm window := by
  intro heff
  exact h heff.1.2.2.1

end LnLean.Proofs.WaveE.E35
