import LnLean

/-!
# LnLean.Proofs.PhaseC3.WatchtowerBreach

English claim.  A revoked commitment that is published on chain is remedied
end to end when

1. a watchtower (or the honest party) observes the breach at a height inside
   the contest delay, and
2. the penalty transaction is accepted by the L1 bridge before the contest
   delay expires.

Under those two *explicit* assumptions, together with the penalty transaction
spending both old main outputs for their total value minus the penalty fee,
the honest party recovers the contested value and the breacher cannot have a
confirmed spend of either old output.  The detection-time and
bridge-acceptance assumptions are fields of `WatchtowerBreachRemedy`
(`detection` and `acceptance`), not axioms: every theorem below is conditional
on them, and the atomic penalty laws are reused from
`LnLean.Proofs.Channel.PenaltyProps` rather than re-proved.

BOLT anchors.
* BOLT 5 §Revoked Transaction Close Handling:
  `refs/bolts/05-onchain.md:510` (a previous commitment besides the most
  current one may be punished with the revocation key),
  `:517` (penalty transaction inputs and single sweep output),
  `:529` (spend the remote main output with the revocation private key),
  `:547` (one penalty transaction may resolve all revoked outputs),
  `:582` (penalty transaction weight).
* BOLT 3 §to_local Output: `refs/bolts/03-transactions.md:113`; §to_remote
  Output: `:136`; §revocationpubkey: `:799`; per-commitment secret
  requirements: `:828`.
* BOLT 2 `revoke_and_ack` reveals the per-commitment secret:
  `refs/bolts/02-peer-protocol.md:3206`.

rust-lightning anchors at pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/chain/channelmonitor.rs:3102` (detecting that the
  counterparty broadcast a revoked state).
* `lightning/src/chain/channelmonitor.rs:5079`
  (`check_spend_counterparty_transaction`, the revoked-commitment path), and
  `:5104`/`:5107` (look up the per-commitment secret and derive the
  revocation key / justice package).
* `lightning/src/chain/channelmonitor.rs:997`
  (`CounterpartyRevokedOutputClaimable`).
* `lightning/src/ln/chan_utils.rs:537`
  (`derive_private_revocation_key`, used by the punisher).

What is explicitly NOT modelled.
* Bitcoin script execution, signature checking, package relay, fee bumping,
  and the concrete shachain/secp256k1 arithmetic; the L1 consequence is the
  named `L1ScriptBridge` argument of the remedy.
* Watchtower liveness.  `Watchtower.live` remains an interface proposition;
  liveness is a field-level assumption (`detected`) plus the report witness,
  never an axiom.
* The contest delay is the parameter `window`, not the `to_self_delay` read
  from the old commitment script; linking the two is a script-semantics
  obligation.
* HTLC-output penalties, chain reorgs, and the economics of `penaltyFee`.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean
open LnLean.Bitcoin
open LnLean.Channel
open LnLean.Proofs.Channel

set_option autoImplicit false

/-! ## The two explicit assumptions -/

/-- The detection-time assumption: an observer (watchtower or the honest
party) sees the published revoked commitment at `detectHeight`, inside the
half-open contest interval `[breachHeight, breachHeight + window)`.  This is
exactly the timeliness part of BOLT 5 revoked-close handling; it is a
structure field so that no theorem can silently assume detection. -/
structure DetectionBeforeDeadline (c : RevokedCommitment) (window : Blocks) where
  /-- Height at which the breach is observed. -/
  detectHeight : Height
  /-- Observation cannot precede the on-chain publication. -/
  breach_le_detect : c.breachHeight ≤ detectHeight
  /-- The contest delay is still open at observation time. -/
  detect_lt_deadline : detectHeight < c.breachHeight + window

/-- The bridge-acceptance assumption: the L1 bridge confirms the penalty
transaction at `confirmHeight`.  `accepted` is the only L1 fact the composition
consumes; script execution and signature checking are abstracted by
`L1ScriptBridge.confirms`. -/
structure BridgeAcceptance (bridge : L1ScriptBridge) (p : PenaltyTx) where
  /-- Height at which the penalty transaction is accepted. -/
  confirmHeight : Height
  /-- The L1 bridge accepts (confirms) the penalty transaction. -/
  accepted : bridge.confirms p.toTx

/-! ## The scenario -/

/-- A complete watchtower breach-remedy scenario.  The first two assumption
groups are explicit fields (`revoked`, `detection`, `acceptance`) and the
remaining fields are the penalty-transaction facts already modelled by
`LnLean.Channel.Penalty`.  No field is an axiom: a value of this structure is
a witness that the assumptions hold. -/
structure WatchtowerBreachRemedy where
  /-- Revocation-key scheme used by the punisher. -/
  scheme : RevocationScheme
  /-- The named L1 no-double-spend bridge. -/
  bridge : L1ScriptBridge
  /-- The published (old) commitment. -/
  c : RevokedCommitment
  /-- The penalty transaction. -/
  p : PenaltyTx
  /-- The punisher's revocation witness. -/
  w : PenaltyWitness
  /-- Contest delay in blocks. -/
  window : Blocks
  /-- The published commitment is revoked. -/
  revoked : breachDetected c
  /-- Who is online at the detection height (modelled discovery route). -/
  online : Height → Prop
  /-- The watchtower interface. -/
  tower : Watchtower
  /-- Explicit detection-time assumption. -/
  detection : DetectionBeforeDeadline c window
  /-- The breach is detected, online or through a watchtower report. -/
  detected : Detectable online tower c detection.detectHeight
  /-- Explicit L1 bridge-acceptance assumption. -/
  acceptance : BridgeAcceptance bridge p
  /-- Detection strictly precedes (or coincides with) acceptance. -/
  detect_le_confirm : detection.detectHeight ≤ acceptance.confirmHeight
  /-- Acceptance happens before the contest delay expires. -/
  confirm_lt_deadline : acceptance.confirmHeight < c.breachHeight + window
  /-- The penalty transaction spends both old main outputs. -/
  penaltySpends : penaltySpendsBoth c p
  /-- The sweep output is the old main-output total minus the penalty fee. -/
  sweepValue : p.sweep.value = c.toLocalValue + c.toRemoteValue - c.penaltyFee

namespace WatchtowerBreachRemedy

/-! ## Detection-time consequences -/

/-- The contest delay is positive: a breach detected strictly before
`breachHeight + window` cannot have `window = 0`. -/
theorem window_pos (r : WatchtowerBreachRemedy) : 0 < r.window := by
  have h : r.c.breachHeight < r.c.breachHeight + r.window :=
    Nat.lt_of_le_of_lt r.detection.breach_le_detect r.detection.detect_lt_deadline
  exact Nat.lt_of_add_lt_add_left (n := r.c.breachHeight) (by simpa using h)

/-- The watchtower detects the breach before the contest delay expires. -/
theorem detection_before_deadline (r : WatchtowerBreachRemedy) :
    r.detection.detectHeight < r.c.breachHeight + r.window :=
  r.detection.detect_lt_deadline

/-- If the honest party is offline at the detection height, the modelled
discovery route must be a watchtower report, hence the tower is live.  This is
the liveness bridge in its conditional form (LN-BREACH-017). -/
theorem offline_detection_implies_live (r : WatchtowerBreachRemedy)
    (hno : ¬ r.online r.detection.detectHeight) : r.tower.live :=
  detected_after_deadline_requires_watchtower r.online r.tower r.c
    r.detection.detectHeight r.detected hno

/-! ## Timeliness and penalty validity -/

/-- The penalty confirms inside the open contest interval: detection is
timely and acceptance follows it before the deadline. -/
theorem timely (r : WatchtowerBreachRemedy) :
    timelyL1Confirmation r.c.breachHeight r.acceptance.confirmHeight r.window :=
  ⟨Nat.le_trans r.detection.breach_le_detect r.detect_le_confirm,
    r.confirm_lt_deadline⟩

/-- The scenario satisfies the core `penaltyValid` predicate.  The
cryptographic key conjunct is discharged by `RevocationScheme.consistent`, so
the remaining core conditions are exactly the scenario fields. -/
theorem penaltyValid (r : WatchtowerBreachRemedy) :
    penaltyValid r.scheme r.c r.p r.w r.acceptance.confirmHeight r.window :=
  (penaltyValid_iff_core r.scheme r.c r.p r.w r.acceptance.confirmHeight
    r.window).2
    ⟨r.revoked, r.penaltySpends, r.sweepValue, r.timely⟩

/-- The breach is punishable by the penalty path. -/
theorem punishable (r : WatchtowerBreachRemedy) :
    punishable r.scheme r.c r.p r.w r.acceptance.confirmHeight r.window :=
  ⟨r.revoked, r.penaltyValid⟩

/-! ## Recovery of the contested value -/

/-- The honest party's sweep pays exactly the two old main outputs minus the
penalty fee. -/
theorem recovers_value (r : WatchtowerBreachRemedy) :
    r.p.sweep.value = r.c.toLocalValue + r.c.toRemoteValue - r.c.penaltyFee :=
  r.sweepValue

/-- No value is created: sweep plus fee equals the contested total. -/
theorem recovers_value_add_fee (r : WatchtowerBreachRemedy) :
    r.p.sweep.value + r.c.penaltyFee =
      r.c.toLocalValue + r.c.toRemoteValue := by
  rw [r.sweepValue]
  exact Int.sub_add_cancel _ _

/-- A non-negative fee leaves the recovery at or below the contested total. -/
theorem recovers_value_le_total (r : WatchtowerBreachRemedy)
    (hfee : 0 ≤ r.c.penaltyFee) :
    r.p.sweep.value ≤ r.c.toLocalValue + r.c.toRemoteValue :=
  penaltyValid_sweep_le_total r.penaltyValid hfee

/-- Under the economic precondition that the fee is non-negative and does not
exceed the contested total, the honest party's recovery is non-negative. -/
theorem recovers_value_nonneg (r : WatchtowerBreachRemedy)
    (hfee : 0 ≤ r.c.penaltyFee)
    (hfee_total : r.c.penaltyFee ≤ r.c.toLocalValue + r.c.toRemoteValue) :
    0 ≤ r.p.sweep.value :=
  penaltyValid_sweep_nonneg r.penaltyValid hfee hfee_total

/-- The recovery covers at least the old `to_local` value minus the fee when
the old `to_remote` value is non-negative. -/
theorem recovers_at_least_toLocal_sub_fee (r : WatchtowerBreachRemedy)
    (hremote : 0 ≤ r.c.toRemoteValue) :
    r.c.toLocalValue - r.c.penaltyFee ≤ r.p.sweep.value :=
  sweep_ge_toLocal_sub_fee r.c r.p r.sweepValue hremote

/-! ## The breacher cannot spend the contested outputs -/

/-- Once the bridge accepts the penalty, no confirmed transaction of the
breacher can spend either old main output. -/
theorem no_breacher_spend (r : WatchtowerBreachRemedy) (b : Tx)
    (hb : BreacherSpend r.c b) : ¬ r.bridge.confirms b :=
  punished_not_breacher_spendable r.bridge r.scheme r.c r.p r.w
    r.acceptance.confirmHeight r.window b r.penaltyValid hb
    r.acceptance.accepted

/-- The `to_local` half of the no-double-spend conclusion. -/
theorem toLocal_unavailable (r : WatchtowerBreachRemedy) (b : Tx)
    (hb : Spends b r.c.toLocal) : ¬ r.bridge.confirms b :=
  penaltyValid_blocks_toLocal_spend r.bridge r.scheme r.c r.p r.w
    r.acceptance.confirmHeight r.window b r.penaltyValid hb
    r.acceptance.accepted

/-- The `to_remote` half of the no-double-spend conclusion. -/
theorem toRemote_unavailable (r : WatchtowerBreachRemedy) (b : Tx)
    (hb : Spends b r.c.toRemote) : ¬ r.bridge.confirms b :=
  penaltyValid_blocks_toRemote_spend r.bridge r.scheme r.c r.p r.w
    r.acceptance.confirmHeight r.window b r.penaltyValid hb
    r.acceptance.accepted

end WatchtowerBreachRemedy

/-! ## The end-to-end composition -/

/-- **Obligation PC3-38-END-TO-END.**  Published revoked commitment plus a
timely watchtower detection plus an accepted penalty transaction implies:
the commitment is a breach, it is punishable, the penalty confirms inside the
contest interval, the honest party's sweep plus fee equals the contested
total, and no breacher transaction spending either old output can confirm.
All assumptions are the explicit fields of `WatchtowerBreachRemedy`. -/
theorem watchtowerBreach_end_to_end (r : WatchtowerBreachRemedy) :
    breachDetected r.c ∧
    punishable r.scheme r.c r.p r.w r.acceptance.confirmHeight r.window ∧
    timelyL1Confirmation r.c.breachHeight r.acceptance.confirmHeight r.window ∧
    r.p.sweep.value + r.c.penaltyFee =
      r.c.toLocalValue + r.c.toRemoteValue ∧
    (∀ b : Tx, BreacherSpend r.c b → ¬ r.bridge.confirms b) :=
  ⟨r.revoked, r.punishable, r.timely, r.recovers_value_add_fee,
    fun _ hb => r.no_breacher_spend _ hb⟩

/-- The same composition with recovery and exclusion stated as separate
conclusions, for integration with the phase-C3 conservation lane. -/
theorem watchtowerBreach_recovers_and_excludes (r : WatchtowerBreachRemedy) :
    r.p.sweep.value = r.c.toLocalValue + r.c.toRemoteValue - r.c.penaltyFee ∧
    (∀ b : Tx, BreacherSpend r.c b → ¬ r.bridge.confirms b) :=
  ⟨r.recovers_value, fun _ hb => r.no_breacher_spend _ hb⟩

end LnLean.Proofs.PhaseC3
