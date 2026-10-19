import LnLean.Channel.State
import LnLean.Proofs.Channel.FeeProps

/-!
# Wave 14 — checked `update_fee` legality and a zero-fee/shared-anchor carrier

Lane `W14-FEE-UPDATE`.  This module is **additive**.  It does not change
`LnLean.Channel.State.Step`, its `updateFee` constructor,
`LnLean.Channel.Fee.updateFee`, or `LnLean.Channel.Commitment.commitmentFee`.

## The gap

`Step.updateFee` (`LnLean/Channel/State.lean:117-121`) is guarded only by
`c.phase = ChannelPhase.normal`.  It accepts any feerate from any sender and
records no paid fee, so the unguarded path cannot express BOLT 2 §3's three
legality requirements:

* the channel is in the `normal` phase;
* the sender is the node responsible for paying the Bitcoin fee (the
  *funder*), and the non-funder MUST NOT send `update_fee`
  (`refs/bolts/02-peer-protocol.md:3271-3277`);
* the sender can afford the new feerate on the receiver's current commitment
  (`refs/bolts/02-peer-protocol.md:3283-3287`), i.e. the paid fee covers the
  BOLT 3 base fee for the new rate and the commitment weight
  (`refs/bolts/03-transactions.md:518-524`).

`LnLean.Proofs.Channel.FeeProps.checkedFeeUpdate` already implements the
third check as an `Option`-returning parameter replacement.  This module
wires it into a channel-level wrapper and proves that the wrapper refines the
existing `Step.updateFee` path.

## Headline declarations

* `FeeUpdateRequest` — sender, requested rate, commitment weight, paid fee.
* `CommitmentVersion`, `CommitmentVersionCarrier`, `baseFeeFor`,
  `anchorCountFor`, `sharedAnchorAmount` — an additive version/zero-fee/
  shared-anchor carrier.
* `FeeUpdateAllowed` — normal phase **and** non-zero-fee version **and**
  correct funder **and** `feeSufficient`.
* `checkedFeeStep` — applies `checkedFeeUpdate` to the local parameters and
  returns the successor channel, or `none`.
* `checkedFeeStep_some_iff` — exact characterisation.
* `checkedFeeStep_refines_updateFee` — a checked step is a `Step.updateFee`
  derivation.
* `nonFunder_update_not_allowed`, `insufficient_update_rejected` — the two
  rejection directions.
* `demo_valid_update_allowed`, `demo_valid_update_refines_Step`,
  `demo_insufficient_update_rejected`, `demo_nonFunder_update_rejected` —
  concrete non-vacuity and rejection witnesses.
* `unguarded_updateFee_admits_insufficient` — the retained, deliberately
  unguarded carrier still admits the same insufficient update; the checked
  wrapper rejects it.  This is an explicit separation, not a weakening.
* `zeroFee_sharedAnchor_separates` — a zero-fee witness has base fee 0 and
  exactly one shared anchor, while the legacy anchored witness has two
  anchors.

## BOLT / LDK anchors

* BOLT 2 §3 `update_fee` (`refs/bolts/02-peer-protocol.md:3250-3310`):
  funder-only send, zero-fee channels MUST NOT send, receiver affordability
  check.
* BOLT 3 §4 `Fee Calculation` (`refs/bolts/03-transactions.md:464-524`):
  flooored base fee; the commitment base fee MUST be 0 when
  `zero_fee_commitments` applies.
* BOLT 3 §2 `shared_anchor` (`refs/bolts/03-transactions.md:178-198`): one
  output for `zero_fee_commitments`, amount `min(remaining, 240)` sat.
* BOLT 2 channel types (`refs/bolts/02-peer-protocol.md:793`, `:1223-1233`):
  `zero_fee_commitments` requires `commitment_feerate_perkw = 0`.
* rust-lightning `fe4900930c6bd5786ec4203274d7cf312776a5a6`:
  `lightning/src/ln/channel.rs:5916-5950` (`validate_update_fee`),
  `:6047-6120` (`can_send_update_fee`),
  `lightning/src/ln/chan_utils.rs:289-298` (`commit_tx_fee_sat`).

## Explicit boundaries (not overclaimed)

* The `Channel` record has **no funder field**.  `funder` is a declared
  local-view parameter supplied by the caller; a production consumer must
  derive it from channel establishment.  The wrapper therefore proves
  "sender equals the declared funder", not "the channel record stores the
  correct funder".
* `Step.updateFee` stores the feerate only in `localEndpoint.params`.  The
  refinement inherits that local-view representation; it does not claim that
  both endpoints' commitment records are updated.
* The affordability check is the **base-fee** check
  `feeForWeight r w <= paid`.  It is not BOLT 3's actual on-chain fee after
  trimming, not the dust-exposure policy, and not the reserve check on the
  funder's output.  Those remain separate consumers
  (`FeeProps.feeUpdateChecksOk`, `FeeTargets.commitmentSigningGate`).
* `CommitmentVersionCarrier` is a sidecar.  `ChannelParams` still has no
  version field, `Commitment` still has no version field, and the catalogue
  `commitmentFee` remains the version-2 fee.  The zero-fee carrier is not
  wired into `Step`.
* `sharedAnchorAmount` implements the BOLT 3 `min(remaining, 240)` rule
  only.  It does not construct a P2A script, and it does not model ephemeral
  dust relay policy.
* The zero-fee version forbids `update_fee`; the module proves that on the
  wrapper.  It does not claim the unguarded `Step.updateFee` constructor is
  removed or that a zero-fee channel cannot reach it.
-/

namespace LnLean.Proofs.Wave14.FeeUpdateLegality

set_option autoImplicit false

open LnLean
open LnLean.Channel

/-! ## Decidability for the concrete witnesses -/

/-- `feeSufficient` is a `Nat` comparison after unfolding.  This instance is
the same one used by `LnLean.Proofs.Channel.FeeTargets`, restated locally so
the concrete `decide` witnesses do not depend on an import edge. -/
instance feeSufficientDecidable (r : FeeRate) (w : Weight) (paid : Msat) :
    Decidable (feeSufficient r w paid) :=
  inferInstanceAs (Decidable ((feeForWeight r w).val ≤ paid.val))

/-! ## Requests and commitment versions -/

/-- An `update_fee` request as the receiver sees it: who sent it, the new
feerate, the commitment weight at which affordability is checked, and the
fee actually paid (in millisatoshis). -/
structure FeeUpdateRequest where
  /-- `local` when the local node sent the update, `remote` otherwise. -/
  sender : Direction
  /-- The requested `feerate_per_kw`. -/
  rate : FeeRate
  /-- The expected commitment weight used by the affordability check. -/
  weight : Weight
  /-- The fee the funder can pay at that weight, in millisatoshis. -/
  paid : Msat
deriving Repr, DecidableEq, BEq

/-- Commitment-version tag.  `v2` is the existing BOLT 3 version-2 form;
`v3ZeroFee` is the `zero_fee_commitments` form.  This is a sidecar: neither
`ChannelParams` nor `Commitment` is changed. -/
inductive CommitmentVersion where
  | v2
  | v3ZeroFee
deriving Repr, DecidableEq, BEq

namespace CommitmentVersion

/-- `true` exactly for the `zero_fee_commitments` form. -/
def isZeroFee : CommitmentVersion → Bool
  | .v2 => false
  | .v3ZeroFee => true

theorem isZeroFee_v2 : isZeroFee .v2 = false := rfl

theorem isZeroFee_v3 : isZeroFee .v3ZeroFee = true := rfl

end CommitmentVersion

/-- The BOLT 3 base fee under a commitment version.  Version 2 uses the
existing floored `feeForWeight`; `zero_fee_commitments` fixes the base fee at
zero (BOLT 3 `03-transactions.md:518-520`). -/
def baseFeeFor (version : CommitmentVersion) (r : FeeRate) (w : Weight) : Msat :=
  match version with
  | .v2 => feeForWeight r w
  | .v3ZeroFee => Msat.zero

theorem baseFeeFor_v2 (r : FeeRate) (w : Weight) :
    baseFeeFor .v2 r w = feeForWeight r w := rfl

theorem baseFeeFor_v3 (r : FeeRate) (w : Weight) :
    baseFeeFor .v3ZeroFee r w = Msat.zero := rfl

/-- On version 2 the additive function is exactly the existing catalogue
`commitmentFee` at the commitment's own weight.  No existing definition is
changed. -/
theorem baseFeeFor_v2_commitmentFee (r : FeeRate) (c : Commitment) :
    baseFeeFor .v2 r c.weight = commitmentFee r c := rfl

/-- Anchor count per commitment version.  Version 2 has the two per-side
`option_anchors` outputs when anchors are negotiated; the zero-fee form has
exactly one `shared_anchor` (BOLT 3 `03-transactions.md:178-198`,
`:351-353`). -/
def anchorCountFor (version : CommitmentVersion) (anchors : Bool) : Nat :=
  match version with
  | .v2 => if anchors then 2 else 0
  | .v3ZeroFee => 1

theorem anchorCountFor_v3 (anchors : Bool) :
    anchorCountFor .v3ZeroFee anchors = 1 := rfl

theorem anchorCountFor_v2_anchors :
    anchorCountFor .v2 true = 2 := rfl

theorem anchorCountFor_v2_noAnchors :
    anchorCountFor .v2 false = 0 := rfl

/-- The BOLT 3 `shared_anchor` amount rule: if the remaining difference is
below 240 sat use it, otherwise 240 sat
(`refs/bolts/03-transactions.md:190-194`). -/
def sharedAnchorAmount (remainingSat : Nat) : Nat :=
  if remainingSat < 240 then remainingSat else 240

theorem sharedAnchorAmount_le (remainingSat : Nat) :
    sharedAnchorAmount remainingSat ≤ 240 := by
  unfold sharedAnchorAmount
  split <;> omega

theorem sharedAnchorAmount_of_lt {remainingSat : Nat} (h : remainingSat < 240) :
    sharedAnchorAmount remainingSat = remainingSat := by
  simp [sharedAnchorAmount, h]

theorem sharedAnchorAmount_of_ge {remainingSat : Nat} (h : 240 ≤ remainingSat) :
    sharedAnchorAmount remainingSat = 240 := by
  simp [sharedAnchorAmount, Nat.not_lt.mpr h]

/-- Concrete fee-0 witness: no remaining value means no shared-anchor
output.  This prevents the `min` rule from being vacuous. -/
theorem sharedAnchorAmount_zero : sharedAnchorAmount 0 = 0 := by
  decide

/-- Concrete maximum witness: a large remaining difference is capped at the
240-sat standard dust limit. -/
theorem sharedAnchorAmount_1000 : sharedAnchorAmount 1000 = 240 := by
  decide

/-- A feerate of zero makes the floored base fee zero.  This is the parameter
side of `zero_fee_commitments`; the version side is `baseFeeFor_v3`. -/
theorem feeForWeight_eq_zero_of_feerate_zero (r : FeeRate) (w : Weight)
    (h : r.msatPerKw = 0) : feeForWeight r w = Msat.zero := by
  unfold feeForWeight Msat.zero
  rw [h]
  simp

/-! ## The additive version carrier -/

/-- A sidecar commitment-version record: the version, whether the legacy
per-side anchors are negotiated, the feerate, and the expected weight.  It
does not replace `Commitment` or `ChannelParams`. -/
structure CommitmentVersionCarrier where
  version : CommitmentVersion
  anchors : Bool
  feerate : FeeRate
  weight : Weight
deriving Repr, DecidableEq, BEq

namespace CommitmentVersionCarrier

/-- The base fee under this carrier's version, rate, and weight. -/
def baseFee (v : CommitmentVersionCarrier) : Msat :=
  baseFeeFor v.version v.feerate v.weight

/-- The anchor output count under this carrier's version and anchor flag. -/
def anchorCount (v : CommitmentVersionCarrier) : Nat :=
  anchorCountFor v.version v.anchors

theorem baseFee_eq_baseFeeFor (v : CommitmentVersionCarrier) :
    v.baseFee = baseFeeFor v.version v.feerate v.weight := rfl

theorem anchorCount_eq_anchorCountFor (v : CommitmentVersionCarrier) :
    v.anchorCount = anchorCountFor v.version v.anchors := rfl

/-- Zero-fee carriers pay a zero base fee regardless of rate or weight. -/
theorem baseFee_zeroFee (v : CommitmentVersionCarrier)
    (hv : v.version = CommitmentVersion.v3ZeroFee) :
    v.baseFee = Msat.zero := by
  cases v with
  | mk version anchors feerate weight =>
      subst hv
      rfl

/-- Legacy carriers keep the existing floored fee. -/
theorem baseFee_legacy (v : CommitmentVersionCarrier)
    (hv : v.version = CommitmentVersion.v2) :
    v.baseFee = feeForWeight v.feerate v.weight := by
  cases v with
  | mk version anchors feerate weight =>
      subst hv
      rfl

/-- Zero-fee carriers emit exactly one shared anchor. -/
theorem anchorCount_zeroFee (v : CommitmentVersionCarrier)
    (hv : v.version = CommitmentVersion.v3ZeroFee) :
    v.anchorCount = 1 := by
  cases v with
  | mk version anchors feerate weight =>
      subst hv
      rfl

end CommitmentVersionCarrier

/-! ## Checked legality -/

/-- `update_fee` is allowed exactly when:

* the channel is in the `normal` phase;
* the commitment version is not `zero_fee_commitments`;
* the sender is the declared funder;
* the paid fee covers the requested rate and weight.

The declaration is a `Prop`; `checkedFeeStep` is its executable counterpart
at the fee check. -/
def FeeUpdateAllowed (c : Channel) (version : CommitmentVersion)
    (funder : Direction) (req : FeeUpdateRequest) : Prop :=
  c.phase = ChannelPhase.normal ∧
  version = CommitmentVersion.v2 ∧
  req.sender = funder ∧
  feeSufficient req.rate req.weight req.paid

/-- Decidability of the legality predicate, so the concrete witnesses below
can be closed by computation. -/
instance feeUpdateAllowedDecidable (c : Channel)
    (version : CommitmentVersion) (funder : Direction)
    (req : FeeUpdateRequest) :
    Decidable (FeeUpdateAllowed c version funder req) :=
  inferInstanceAs (Decidable (c.phase = ChannelPhase.normal ∧
    version = CommitmentVersion.v2 ∧ req.sender = funder ∧
    feeSufficient req.rate req.weight req.paid))

/-- Apply a checked `update_fee` to the channel.  The phase, version, and
funder gates are checked first; the fee affordability check is delegated to
the existing `checkedFeeUpdate`.  A successful result is the same successor
as `Step.updateFee` (`updateChannelFee`). -/
def checkedFeeStep (c : Channel) (version : CommitmentVersion)
    (funder : Direction) (req : FeeUpdateRequest) : Option Channel :=
  if c.phase = ChannelPhase.normal ∧ version = CommitmentVersion.v2 ∧
      req.sender = funder then
    (checkedFeeUpdate c.localEndpoint.params req.rate req.weight req.paid).map
      (fun p =>
        { c with localEndpoint := { c.localEndpoint with params := p } })
  else
    none

/-- Exact characterisation of the checked wrapper: it succeeds iff the
legality predicate holds and the successor is the existing
`updateChannelFee` result. -/
theorem checkedFeeStep_some_iff {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} :
    checkedFeeStep c version funder req = some c' ↔
      FeeUpdateAllowed c version funder req ∧
        c' = updateChannelFee c req.rate := by
  unfold checkedFeeStep
  by_cases hg : c.phase = ChannelPhase.normal ∧
      version = CommitmentVersion.v2 ∧ req.sender = funder
  · rw [if_pos hg]
    unfold checkedFeeUpdate
    by_cases hf : (feeForWeight req.rate req.weight).val ≤ req.paid.val
    · rw [if_pos hf]
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro h
        refine ⟨⟨hg.1, hg.2.1, hg.2.2, hf⟩, ?_⟩
        rw [← h]
        rfl
      · rintro ⟨⟨_, _, _, hpass⟩, rfl⟩
        rfl
    · rw [if_neg hf]
      constructor
      · intro h
        rw [Option.map_none] at h
        cases h
      · rintro ⟨⟨_, _, _, hpass⟩, _⟩
        exact absurd hpass hf
  · rw [if_neg hg]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨h1, h2, h3, _⟩, _⟩
      exact absurd ⟨h1, h2, h3⟩ hg

/-- A checked step is a derivation of the existing `Step.updateFee` path. -/
theorem checkedFeeStep_refines_updateFee {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    Step c (ProtocolEvent.updateFee req.rate) c' := by
  rcases checkedFeeStep_some_iff.mp h with ⟨⟨hphase, _, _, _⟩, rfl⟩
  exact Step.updateFee c hphase req.rate

/-- A successful checked step installs the requested feerate. -/
theorem checkedFeeStep_feerate {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    c'.localEndpoint.params.feerate = req.rate := by
  rcases checkedFeeStep_some_iff.mp h with ⟨_, rfl⟩
  rfl

/-- A successful checked step preserves the phase. -/
theorem checkedFeeStep_phase {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    c'.phase = c.phase := by
  rcases checkedFeeStep_some_iff.mp h with ⟨_, rfl⟩
  rfl

/-- A successful checked step has a fee-sufficient paid amount. -/
theorem checkedFeeStep_sufficient {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    feeSufficient req.rate req.weight req.paid := by
  rcases checkedFeeStep_some_iff.mp h with ⟨⟨_, _, _, hpass⟩, _⟩
  exact hpass

/-- **Non-funder rejection.**  If the sender is not the declared funder, the
update is not allowed. -/
theorem nonFunder_update_not_allowed {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} (hne : req.sender ≠ funder) :
    ¬ FeeUpdateAllowed c version funder req := by
  rintro ⟨_, _, hs, _⟩
  exact hne hs

/-- The executable wrapper rejects a non-funder. -/
theorem nonFunder_checkedFeeStep_none {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} (hne : req.sender ≠ funder) :
    checkedFeeStep c version funder req = none := by
  unfold checkedFeeStep
  have hg : ¬ (c.phase = ChannelPhase.normal ∧
      version = CommitmentVersion.v2 ∧ req.sender = funder) := by
    rintro ⟨_, _, hs⟩
    exact hne hs
  rw [if_neg hg]

/-- **Insufficient-fee rejection.**  If the paid fee does not cover the
requested rate and weight, the wrapper returns `none`. -/
theorem insufficient_update_rejected {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : ¬ feeSufficient req.rate req.weight req.paid) :
    checkedFeeStep c version funder req = none := by
  unfold checkedFeeStep
  by_cases hg : c.phase = ChannelPhase.normal ∧
      version = CommitmentVersion.v2 ∧ req.sender = funder
  · rw [if_pos hg]
    unfold checkedFeeUpdate
    unfold feeSufficient at h
    rw [if_neg h]
    rfl
  · rw [if_neg hg]

/-- **Zero-fee rejection.**  BOLT 2 forbids `update_fee` entirely on a
`zero_fee_commitments` channel (`02-peer-protocol.md:3271-3274`). -/
theorem zeroFee_update_not_allowed {c : Channel} {funder : Direction}
    {req : FeeUpdateRequest} :
    ¬ FeeUpdateAllowed c CommitmentVersion.v3ZeroFee funder req := by
  rintro ⟨_, hv, _⟩
  cases hv

/-- The executable wrapper rejects every update on the zero-fee version. -/
theorem zeroFee_checkedFeeStep_none {c : Channel} {funder : Direction}
    {req : FeeUpdateRequest} :
    checkedFeeStep c CommitmentVersion.v3ZeroFee funder req = none := by
  unfold checkedFeeStep
  have hg : ¬ (c.phase = ChannelPhase.normal ∧
      CommitmentVersion.v3ZeroFee = CommitmentVersion.v2 ∧
      req.sender = funder) := by
    rintro ⟨_, hv, _⟩
    cases hv
  rw [if_neg hg]

/-- The contrapositive in the useful direction: every successful checked
step has a funder sender and a sufficient paid fee. -/
theorem checkedFeeStep_sound {c c' : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest}
    (h : checkedFeeStep c version funder req = some c') :
    req.sender = funder ∧ feeSufficient req.rate req.weight req.paid := by
  rcases checkedFeeStep_some_iff.mp h with ⟨⟨_, _, hs, hpass⟩, _⟩
  exact ⟨hs, hpass⟩

/-- An allowed request produces the checked successor. -/
theorem checkedFeeStep_eq_some_of_allowed {c : Channel}
    {version : CommitmentVersion} {funder : Direction}
    {req : FeeUpdateRequest} (h : FeeUpdateAllowed c version funder req) :
    checkedFeeStep c version funder req = some (updateChannelFee c req.rate) :=
  checkedFeeStep_some_iff.mpr ⟨h, rfl⟩

/-! ## Concrete witnesses -/

/-- Parameters for the demo channel.  The feerate is the negotiated current
rate; the demo requests below replace it. -/
def demoParams (feerate : Nat) : ChannelParams :=
  { dustLimitSat := 546
    channelReserveSat := 1000
    toSelfDelay := 144
    maxHtlcValue := ⟨1_000_000_000⟩
    htlcMinimum := ⟨1000⟩
    feerate := ⟨feerate⟩
    anchorOutputs := false }

/-- The demo endpoint.  Node and funding keys are payload placeholders, as in
the other Wave 14 witnesses; key derivation is not modelled. -/
def demoEndpoint (feerate : Nat) : Endpoint :=
  { nodeId := ⟨ByteArray.empty⟩
    fundingPubKey := ⟨ByteArray.empty⟩
    paymentBasepoint := ⟨ByteArray.empty⟩
    delayedPaymentBasepoint := ⟨ByteArray.empty⟩
    params := demoParams feerate }

/-- A normal-phase, zero-HTLC channel used only for the concrete witnesses. -/
def demoChannel : Channel :=
  { channelId := ⟨ByteArray.empty⟩
    funding := { txid := ByteArray.empty, index := 0 }
    fundingValue := ⟨100_000_000⟩
    localEndpoint := demoEndpoint 1000
    remoteEndpoint := demoEndpoint 1000
    phase := ChannelPhase.normal
    localCommitmentNumber := 0
    remoteCommitmentNumber := 0
    balance :=
      { localBalance := ⟨50_000_000⟩
        remoteBalance := ⟨50_000_000⟩ }
    htlcs := [] }

/-- Weight 724 (zero HTLCs, no anchors) at 1000 msat/kw requires 724 msat;
1000 msat is sufficient. -/
def demoValidRequest : FeeUpdateRequest :=
  { sender := Direction.local
    rate := ⟨1000⟩
    weight := commitmentWeight false 0
    paid := ⟨1000⟩ }

/-- The same weight at 2000 msat/kw requires 1448 msat; 1000 msat is
insufficient. -/
def demoInsufficientRequest : FeeUpdateRequest :=
  { sender := Direction.local
    rate := ⟨2000⟩
    weight := commitmentWeight false 0
    paid := ⟨1000⟩ }

/-- A sufficient request sent by the non-funder. -/
def demoNonFunderRequest : FeeUpdateRequest :=
  { sender := Direction.remote
    rate := ⟨1000⟩
    weight := commitmentWeight false 0
    paid := ⟨1000⟩ }

/-- The demo witness for the zero-fee version: feerate 0, no legacy anchors. -/
def zeroFeeWitness : CommitmentVersionCarrier :=
  { version := CommitmentVersion.v3ZeroFee
    anchors := false
    feerate := ⟨0⟩
    weight := commitmentWeight false 0 }

/-- The legacy anchored witness: version 2 with `option_anchors`. -/
def legacyAnchoredWitness : CommitmentVersionCarrier :=
  { version := CommitmentVersion.v2
    anchors := true
    feerate := ⟨1000⟩
    weight := commitmentWeight true 0 }

/-- **Non-vacuity: a valid update is allowed.** -/
theorem demo_valid_update_allowed :
    FeeUpdateAllowed demoChannel CommitmentVersion.v2 Direction.local
      demoValidRequest := by
  decide

/-- **Non-vacuity: the valid update produces the checked successor.** -/
theorem demo_valid_update_step :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoValidRequest =
      some (updateChannelFee demoChannel ⟨1000⟩) :=
  checkedFeeStep_eq_some_of_allowed demo_valid_update_allowed

/-- **The concrete valid update refines `Step.updateFee`.** -/
theorem demo_valid_update_refines_Step :
    ∃ c' : Channel,
      Step demoChannel (ProtocolEvent.updateFee ⟨1000⟩) c' ∧
        c' = updateChannelFee demoChannel ⟨1000⟩ :=
  ⟨_, checkedFeeStep_refines_updateFee demo_valid_update_step, rfl⟩

/-- **The concrete insufficient update is rejected.** -/
theorem demo_insufficient_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoInsufficientRequest = none :=
  insufficient_update_rejected (by decide)

/-- **The concrete non-funder update is rejected.** -/
theorem demo_nonFunder_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v2 Direction.local
        demoNonFunderRequest = none :=
  nonFunder_checkedFeeStep_none (by decide)

/-- **The zero-fee version rejects the otherwise-valid update.** -/
theorem demo_zeroFee_update_rejected :
    checkedFeeStep demoChannel CommitmentVersion.v3ZeroFee Direction.local
        demoValidRequest = none :=
  zeroFee_checkedFeeStep_none

/-- **Retained unguarded path.**  The existing `Step.updateFee` constructor
still admits the insufficient update, because it records neither the sender
nor the paid fee.  The checked wrapper rejects the same request
(`demo_insufficient_update_rejected`); this separation is intentional and is
not removed by this lane. -/
theorem unguarded_updateFee_admits_insufficient :
    ∃ c' : Channel,
      Step demoChannel (ProtocolEvent.updateFee ⟨2000⟩) c' :=
  ⟨_, Step.updateFee demoChannel rfl ⟨2000⟩⟩

/-- **Zero-fee / shared-anchor separation.**  The zero-fee witness pays a
zero base fee and has exactly one shared anchor; the legacy anchored witness
has two per-side anchors.  Both facts are concrete and computable. -/
theorem zeroFee_sharedAnchor_separates :
    zeroFeeWitness.version = CommitmentVersion.v3ZeroFee ∧
      zeroFeeWitness.baseFee = Msat.zero ∧
      zeroFeeWitness.anchorCount = 1 ∧
      legacyAnchoredWitness.anchorCount = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Concrete shared-anchor amount witnesses.**  Zero remaining value pays
nothing; a large remaining value is capped at 240 sat. -/
theorem sharedAnchorAmount_witnesses :
    sharedAnchorAmount 0 = 0 ∧ sharedAnchorAmount 1000 = 240 :=
  ⟨sharedAnchorAmount_zero, sharedAnchorAmount_1000⟩

/-! ## Axiom audit -/

#print axioms checkedFeeStep_some_iff
#print axioms checkedFeeStep_refines_updateFee
#print axioms nonFunder_update_not_allowed
#print axioms insufficient_update_rejected
#print axioms zeroFee_update_not_allowed
#print axioms demo_valid_update_allowed
#print axioms demo_valid_update_refines_Step
#print axioms demo_insufficient_update_rejected
#print axioms demo_nonFunder_update_rejected
#print axioms unguarded_updateFee_admits_insufficient
#print axioms zeroFee_sharedAnchor_separates

end LnLean.Proofs.Wave14.FeeUpdateLegality
