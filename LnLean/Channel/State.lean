import LnLean.Channel.Types
import LnLean.Channel.HTLC

/-!
# LnLean.Channel.State

English claim.  The BOLT 2 channel lifecycle is a *relation* between
channel records, not a Boolean accept/reject function.  `Step c e c'` holds
exactly when event `e` is permitted in channel state `c` and produces the
successor `c'`.  A transition that BOLT 2 forbids (for example
`funding_locked` before `funding_created`, or `commitment_signed` outside
the `normal` phase) simply has no derivation; it is not hidden inside a
`reject` branch.  `Reachable` is the reflexive-transitive closure of `Step`.

BOLT sections.
* BOLT 2 §2 `Channel Establishment v1` (`02-peer-protocol.md:629-1135`):
  `open_channel`, `accept_channel`, `funding_created`, `funding_signed`,
  `channel_ready` (the message historically named `funding_locked`, see
  `02-peer-protocol.md:1046-1048`).
* BOLT 2 §3 `Channel Operations`:
  `commitment_signed` (`02-peer-protocol.md:3097-3205`),
  `revoke_and_ack` (`:3206-3249`), `update_fee` (`:3250-3265`),
  `shutdown` (`:2136-2230`), `closing_signed` (`:2411-2460`).
* BOLT 2 §3 HTLC messages, in the additive `UpdateStep` layer below:
  `update_add_htlc` (`:2739-2831`), `update_fulfill_htlc` (`:2913-2930`),
  `update_fail_htlc` (`:2944-2960`).

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:799` (`enum ChannelState`), `:1552`
  (`enum ChannelPhase`), `:725-731` (the two shutdown flags),
  `:773-776` (`AwaitingRemoteRevoke` lock on a second `commitment_signed`).
* `lightning/src/ln/channelmanager.rs` is the message dispatcher; the
  individual handlers are in `channel.rs` (for example
  `funding_signed`/`funding_created` handling around `channel.rs:1552-1700`).

What is NOT modelled.
* The HTLC update messages as constructors of `Step`.  They live in the
  additive `UpdateStep` relation below, because the lifecycle relation is
  deliberately balance- and HTLC-preserving (see the section comment).  The
  commitment round that commits a pending update is the separate ordered
  `DanceStep` layer at the end of the file; the pending-update queue that the
  round drains is still abstract.
* Message retransmission, `channel_reestablish`, and the hold/release of
  `commitment_signed` while `AwaitingRemoteRevoke`: the model records which
  event is legal but not the queue of deferred updates.
* Per-commitment secret rotation and signature verification; those belong
  to `Revocation` and `Crypto`.
* Splicing, quiescence, dual funding, and `option_simple_close`.
* `closing_signed` fee negotiation is one event here; the range of
  acceptable closing fees is in `Fee`.
-/

namespace LnLean.Channel

set_option autoImplicit false

open LnLean

/-! ## Events -/

/-- The subset of BOLT 2 messages that affect channel state in this model.
Each message is a distinct constructor whenever its effect differs; in
particular `commitmentSigned` and `revokeAndAck` are not collapsed. -/
inductive ProtocolEvent where
  | openChannel
  | acceptChannel
  | fundingCreated
  | fundingSigned
  | fundingLocked
  | commitmentSigned
  | revokeAndAck
  | updateFee (newRate : FeeRate)
  | shutdown
  | closingSigned
deriving Repr, DecidableEq, BEq

/-! ## Transition relation -/

/-- `Step c e c'`: event `e` takes channel `c` to `c'`.  Every constructor
carries the phase precondition that BOLT 2 imposes.  Consequently a proof
of `Step c e c'` is a certificate that the message is legal, and the
absence of a constructor is exactly the statement that it is illegal. -/
inductive Step : Channel → ProtocolEvent → Channel → Prop where
  /-- `open_channel` is sent while the channel is still being negotiated. -/
  | openChannel (c : Channel) (h : c.phase = ChannelPhase.negotiating) :
      Step c ProtocolEvent.openChannel c
  /-- `accept_channel` is the peer's reply in the same phase. -/
  | acceptChannel (c : Channel) (h : c.phase = ChannelPhase.negotiating) :
      Step c ProtocolEvent.acceptChannel c
  /-- `funding_created` moves to the lock-in wait. -/
  | fundingCreated (c : Channel) (h : c.phase = ChannelPhase.negotiating) :
      Step c ProtocolEvent.fundingCreated { c with phase := ChannelPhase.awaitingLockin }
  /-- `funding_signed` only makes sense after `funding_created`. -/
  | fundingSigned (c : Channel) (h : c.phase = ChannelPhase.awaitingLockin) :
      Step c ProtocolEvent.fundingSigned c
  /-- `funding_locked` (BOLT 2's `channel_ready`) enters normal operation. -/
  | fundingLocked (c : Channel) (h : c.phase = ChannelPhase.awaitingLockin) :
      Step c ProtocolEvent.fundingLocked { c with phase := ChannelPhase.normal }
  /-- Signing the *remote* commitment advances the remote commitment
  counter.  BOLT 2: `commitment_signed` "has changes for the remote
  commitment". -/
  | commitmentSigned (c : Channel) (h : c.phase = ChannelPhase.normal) :
      Step c ProtocolEvent.commitmentSigned
        { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }
  /-- Completing the round advances the *local* commitment counter: the
  `revoke_and_ack` lets the sender apply its pending updates to its own
  commitment (`02-peer-protocol.md:3206-3215`). -/
  | revokeAndAck (c : Channel) (h : c.phase = ChannelPhase.normal) :
      Step c ProtocolEvent.revokeAndAck
        { c with localCommitmentNumber := c.localCommitmentNumber + 1 }
  /-- `update_fee` replaces the feerate; it is not an HTLC and is never
  closed (`02-peer-protocol.md:3255-3260`).  The fee is paid by the funder,
  which is a local-view parameter in this model. -/
  | updateFee (c : Channel) (h : c.phase = ChannelPhase.normal) (r : FeeRate) :
      Step c (ProtocolEvent.updateFee r)
        { c with localEndpoint :=
            { c.localEndpoint with
              params := { c.localEndpoint.params with feerate := r } } }
  /-- `shutdown` stops new HTLCs and begins closing. -/
  | shutdown (c : Channel) (h : c.phase = ChannelPhase.normal) :
      Step c ProtocolEvent.shutdown { c with phase := ChannelPhase.shuttingDown }
  /-- `closing_signed` completes a mutual close. -/
  | closingSigned (c : Channel) (h : c.phase = ChannelPhase.shuttingDown) :
      Step c ProtocolEvent.closingSigned { c with phase := ChannelPhase.closed }

/-! ## Reachability -/

/-- Reflexive-transitive closure of `Step`.  `Reachable a b` means some
finite sequence of BOLT 2 events takes `a` to `b`. -/
inductive Reachable : Channel → Channel → Prop where
  | refl (c : Channel) : Reachable c c
  | step {a b c : Channel} {e : ProtocolEvent} :
      Reachable a b → Step b e c → Reachable a c

namespace Reachable

theorem trans {a b c : Channel} (hab : Reachable a b) (hbc : Reachable b c) :
    Reachable a c := by
  induction hbc with
  | refl => exact hab
  | step _ hs ih => exact Reachable.step ih hs

theorem of_step {a b : Channel} {e : ProtocolEvent} (h : Step a e b) :
    Reachable a b :=
  Reachable.step (Reachable.refl a) h

end Reachable

/-! ## Phase order -/

/-- Numeric rank of a phase.  It is used only to state that the lifecycle
does not move backwards; the transition relation itself does not depend on
this function. -/
def phaseRank : ChannelPhase → Nat
  | .negotiating => 0
  | .awaitingLockin => 1
  | .normal => 2
  | .shuttingDown => 3
  | .closed => 4

/-- Every legal step is non-decreasing in `phaseRank`. -/
theorem step_phaseRank_le {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : phaseRank c.phase ≤ phaseRank c'.phase := by
  cases h <;> simp_all [phaseRank]

/-- `Reachable` preserves the phase order. -/
theorem Reachable.phaseRank_le {a b : Channel} (h : Reachable a b) :
    phaseRank a.phase ≤ phaseRank b.phase := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih => exact Nat.le_trans ih (step_phaseRank_le hs)

/-! ## Illegal transitions have no derivation -/

/-- Nothing follows a closed channel. -/
theorem no_step_from_closed (c c' : Channel) (e : ProtocolEvent)
    (h : c.phase = ChannelPhase.closed) : ¬ Step c e c' := by
  intro hs
  cases hs <;> simp_all

/-- `funding_locked` requires the lock-in wait. -/
theorem step_fundingLocked_requires_awaitingLockin {c c' : Channel}
    (h : Step c ProtocolEvent.fundingLocked c') :
    c.phase = ChannelPhase.awaitingLockin := by
  cases h
  assumption

/-- `commitment_signed` is illegal before the channel is normal. -/
theorem step_commitmentSigned_requires_normal {c c' : Channel}
    (h : Step c ProtocolEvent.commitmentSigned c') :
    c.phase = ChannelPhase.normal := by
  cases h
  assumption

/-- `revoke_and_ack` is illegal before the channel is normal. -/
theorem step_revokeAndAck_requires_normal {c c' : Channel}
    (h : Step c ProtocolEvent.revokeAndAck c') :
    c.phase = ChannelPhase.normal := by
  cases h
  assumption

/-- `shutdown` is only legal from normal operation. -/
theorem step_shutdown_requires_normal {c c' : Channel}
    (h : Step c ProtocolEvent.shutdown c') :
    c.phase = ChannelPhase.normal := by
  cases h
  assumption

/-- `closing_signed` is only legal while shutting down. -/
theorem step_closingSigned_requires_shuttingDown {c c' : Channel}
    (h : Step c ProtocolEvent.closingSigned c') :
    c.phase = ChannelPhase.shuttingDown := by
  cases h
  assumption

/-- No transition can decrease either commitment counter. -/
theorem step_localCommitmentNumber_le {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c.localCommitmentNumber ≤ c'.localCommitmentNumber := by
  cases h <;> simp

theorem step_remoteCommitmentNumber_le {c c' : Channel} {e : ProtocolEvent}
    (h : Step c e c') : c.remoteCommitmentNumber ≤ c'.remoteCommitmentNumber := by
  cases h <;> simp

/-- `Reachable` is monotone in both counters. -/
theorem Reachable.localCommitmentNumber_le {a b : Channel} (h : Reachable a b) :
    a.localCommitmentNumber ≤ b.localCommitmentNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih => exact Nat.le_trans ih (step_localCommitmentNumber_le hs)

theorem Reachable.remoteCommitmentNumber_le {a b : Channel} (h : Reachable a b) :
    a.remoteCommitmentNumber ≤ b.remoteCommitmentNumber := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ hs ih => exact Nat.le_trans ih (step_remoteCommitmentNumber_le hs)

/-! ## Additive HTLC update layer (`MODEL-02`)

`Step` is the *lifecycle* relation: every existing theorem about it (balance,
HTLC-list, reserve, exposure, and ledger preservation, plus the negative
counterexamples in `LnLean.Proofs.WaveD.D14` and
`LnLean.Proofs.WaveE.E37`) depends on the fact that it changes only the phase,
the commitment counters, and the feerate.  Adding `update_add_htlc` as a
constructor of `Step` would therefore invalidate those results.

The BOLT 2 HTLC messages are modelled here as a separate, additive relation
`UpdateStep` over the same `Channel` record.  It embeds the lifecycle relation
(`UpdateStep.lifecycle`) and adds `update_add_htlc`, `update_fulfill_htlc`, and
`update_fail_htlc` with the ledger effects of the successor functions in
`LnLean.Proofs.Channel.ReserveProps` and `LnLean.Proofs.WaveE.E37`.  The event
type is separate (`UpdateEvent`, not `ProtocolEvent`) for the same reason: the
executable schedule model in `LnLean.Proofs.Liveness` matches `ProtocolEvent`
exhaustively.

The distinctive guards are carried by `AffordableAdd` (positive amount,
`cltv_expiry` bound, `htlc_minimum_msat`, offered-balance coverage, reserve,
and `max_htlc_value_in_flight_msat`).  Settlement transitions take an index
into the HTLC list and require that the entry is pending. -/

/-- Pending HTLC value: the sum of the `offered` and `received` amounts, in
millisatoshis.  This is the in-flight bucket of the channel ledger. -/
def pendingHtlcValueOf (c : Channel) : Nat :=
  ((c.htlcs.filter
      (fun h => h.state = HTLCState.offered ∨ h.state = HTLCState.received)).map
    (fun h => h.amount.val)).sum

/-- The settled balance that funds an HTLC offered in direction `d`.  A local
offer spends the local balance; a remote offer spends the remote balance. -/
def offeredBalance (c : Channel) : Direction → Msat
  | .local => c.balance.localBalance
  | .remote => c.balance.remoteBalance

/-- The reserve the offering side must keep after the add.  BOLT 2: the
*receiver* advertises `channel_reserve_satoshis`, so a local offer must leave
`localReserveSat` and a remote offer must leave `remoteReserveSat`. -/
def offeringReserveSat (c : Channel) : Direction → Nat
  | .local => c.remoteEndpoint.params.channelReserveSat
  | .remote => c.localEndpoint.params.channelReserveSat

/-- The parameters of the endpoint that receives the offered HTLC. -/
def receiverParams (c : Channel) : Direction → ChannelParams
  | .local => c.remoteEndpoint.params
  | .remote => c.localEndpoint.params

/-- BOLT 2 affordability of `update_add_htlc` in direction `dir`.

* `positive`: the amount is non-zero (`02-peer-protocol.md:2824`).
* `cltvBelowMaximum`: `cltv_expiry < 500000000` (`:2824`).
* `atLeastHtlcMinimum`: the receiver's `htlc_minimum_msat` (`:2802`).
* `fitsOffered`: the amount is covered by the offering side's settled balance,
  so the committed balance drop does not truncate.
* `leavesReserve`: the post-add balance still meets the receiver's reserve
  (`:884-896`).
* `withinInFlight`: the total in-flight value after the add stays within the
  receiver's `max_htlc_value_in_flight_msat` (`:2829-2831`). -/
structure AffordableAdd (c : Channel) (dir : Direction) (amount : Msat)
    (cltvExpiry : Height) : Prop where
  /-- The amount is strictly positive. -/
  positive : 0 < amount.val
  /-- BOLT 2's `cltv_expiry` bound. -/
  cltvBelowMaximum : cltvExpiry < MAX_CLTV_EXPIRY
  /-- The receiver's `htlc_minimum_msat` is respected. -/
  atLeastHtlcMinimum : (receiverParams c dir).htlcMinimum.val ≤ amount.val
  /-- The amount fits the offering side's settled balance. -/
  fitsOffered : amount.val ≤ (offeredBalance c dir).val
  /-- The offering side stays above its reserve. -/
  leavesReserve :
    offeringReserveSat c dir * Msat.MSAT_PER_SAT + amount.val ≤
      (offeredBalance c dir).val
  /-- The receiver's total in-flight bound is respected after the add. -/
  withinInFlight :
    pendingHtlcValueOf c + amount.val ≤ (receiverParams c dir).maxHtlcValue.val

/-- The successor channel of `update_add_htlc`: debit the offering balance and
append one pending HTLC (`offered` locally, `received` for a remote offer).
This generalises `LnLean.Proofs.WaveE.E37.committedAdd` to both directions; the
local case is proved definitionally equal in
`LnLean.Proofs.Channel.StateTransitionTargets`. -/
def updateAddHtlc (c : Channel) (dir : Direction) (amount : Msat)
    (ph : PaymentHash) (cltv : Height) : Channel :=
  { c with
    balance :=
      match dir with
      | .local =>
          { c.balance with
            localBalance := ⟨c.balance.localBalance.val - amount.val⟩ }
      | .remote =>
          { c.balance with
            remoteBalance := ⟨c.balance.remoteBalance.val - amount.val⟩ }
    htlcs := c.htlcs ++
      [{ direction := dir
         amount := amount
         paymentHash := ph
         cltvExpiry := cltv
         state := match dir with
           | .local => HTLCState.offered
           | .remote => HTLCState.received }] }

/-- Replace the HTLC at index `i` by `f` applied to it; out-of-range indices
leave the list unchanged. -/
def mapHtlcAt (i : Nat) (f : HTLC → HTLC) (hs : List HTLC) : List HTLC :=
  match hs, i with
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, k + 1 => x :: mapHtlcAt k f xs

/-- Mark the HTLC at index `i` as settled in state `st`. -/
def setHtlcStateAt (hs : List HTLC) (i : Nat) (st : HTLCState) : List HTLC :=
  mapHtlcAt i (fun h => { h with state := st }) hs

/-- The successor of `update_fail_htlc` at index `i`: mark the pending HTLC
`failed` and return its amount to the offering side.  Out-of-range indices
leave the channel unchanged; the transition guard rules them out. -/
def failHtlcAt (c : Channel) (i : Nat) : Channel :=
  match c.htlcs[i]? with
  | none => c
  | some h =>
      { c with
        htlcs := setHtlcStateAt c.htlcs i HTLCState.failed
        balance :=
          match h.direction with
          | .local =>
              { c.balance with
                localBalance :=
                  ⟨c.balance.localBalance.val + h.amount.val⟩ }
          | .remote =>
              { c.balance with
                remoteBalance :=
                  ⟨c.balance.remoteBalance.val + h.amount.val⟩ } }

/-- The successor of `update_fulfill_htlc` at index `i`: mark the pending HTLC
`fulfilled` and credit its amount to the *receiving* side.  Out-of-range
indices leave the channel unchanged; the transition guard rules them out. -/
def fulfillHtlcAt (c : Channel) (i : Nat) : Channel :=
  match c.htlcs[i]? with
  | none => c
  | some h =>
      { c with
        htlcs := setHtlcStateAt c.htlcs i HTLCState.fulfilled
        balance :=
          match h.direction with
          | .local =>
              { c.balance with
                remoteBalance :=
                  ⟨c.balance.remoteBalance.val + h.amount.val⟩ }
          | .remote =>
              { c.balance with
                localBalance :=
                  ⟨c.balance.localBalance.val + h.amount.val⟩ } }

/-- Events of the additive HTLC update layer.  `lifecycle` embeds the
`ProtocolEvent` vocabulary; the three update messages carry their BOLT 2
payload so that a transition has a unique target. -/
inductive UpdateEvent where
  | lifecycle (e : ProtocolEvent)
  | addHtlc (direction : Direction) (amount : Msat) (paymentHash : PaymentHash)
      (cltvExpiry : Height)
  | fulfillHtlc (index : Nat) (preimage : Preimage)
  | failHtlc (index : Nat)
deriving Repr

/-- `UpdateStep hashFn c e c'`: the BOLT 2 update message `e` is legal in state
`c` and produces `c'`.  `hashFn` is the caller-supplied SHA-256 used only by
`update_fulfill_htlc`; as in `LnLean.Channel.HTLC.fulfillHTLC`, preimage
soundness is conditional on `hashFn p.bytes = paymentHash`.

`lifecycle` is the embedding of the unchanged `Step` relation, so every
lifecycle transition remains available and every existing counterexample is
untouched. -/
inductive UpdateStep (hashFn : ByteArray → ByteArray) :
    Channel → UpdateEvent → Channel → Prop where
  /-- Every lifecycle step is an update-layer step. -/
  | lifecycle {c c' : Channel} {e : ProtocolEvent} (h : Step c e c') :
      UpdateStep hashFn c (.lifecycle e) c'
  /-- BOLT 2 `update_add_htlc`.  Only legal in the `normal` phase and only for
  an affordable amount. -/
  | update_add_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (dir : Direction) (amount : Msat) (ph : PaymentHash) (cltv : Height)
      (haff : AffordableAdd c dir amount cltv) :
      UpdateStep hashFn c (.addHtlc dir amount ph cltv)
        (updateAddHtlc c dir amount ph cltv)
  /-- BOLT 2 `update_fulfill_htlc`: a pending HTLC at index `i` is settled by a
  32-byte preimage hashing to its payment hash. -/
  | update_fulfill_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (i : Nat) (h : HTLC) (p : Preimage)
      (hi : c.htlcs[i]? = some h) (hpending : h.isPending)
      (hpre : p.Valid ∧ hashFn p.bytes = h.paymentHash.bytes) :
      UpdateStep hashFn c (.fulfillHtlc i p) (fulfillHtlcAt c i)
  /-- BOLT 2 `update_fail_htlc`: a pending HTLC at index `i` is failed and its
  amount returns to the offering side. -/
  | update_fail_htlc (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (i : Nat) (h : HTLC) (hi : c.htlcs[i]? = some h)
      (hpending : h.isPending) :
      UpdateStep hashFn c (.failHtlc i) (failHtlcAt c i)

/-- Reflexive-transitive closure of `UpdateStep`. -/
inductive UpdateReachable (hashFn : ByteArray → ByteArray) :
    Channel → Channel → Prop where
  | refl (c : Channel) : UpdateReachable hashFn c c
  | step {a b c : Channel} {e : UpdateEvent} :
      UpdateReachable hashFn a b → UpdateStep hashFn b e c →
        UpdateReachable hashFn a c

/-- Additive spelling of the requested constructor: `Step.update_add_htlc`
builds the `update_add_htlc` transition of the update layer.  It is a
definition, not a constructor of the lifecycle inductive `Step`, because a new
`Step` constructor would invalidate the lifecycle-only preservation theorems
and the executable `step?` model elsewhere in the tree. -/
abbrev Step.update_add_htlc (hashFn : ByteArray → ByteArray) (c : Channel)
    (hphase : c.phase = ChannelPhase.normal) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (haff : AffordableAdd c dir amount cltv) :
    UpdateStep hashFn c (.addHtlc dir amount ph cltv)
      (updateAddHtlc c dir amount ph cltv) :=
  UpdateStep.update_add_htlc c hphase dir amount ph cltv haff

/-! ## Additive commitment-round layer (`MODEL-03`)

`Step` records `commitment_signed` and `revoke_and_ack` as independent
lifecycle events: either may be replayed from any `normal` channel, and their
two counters are not related.  BOLT 2 §3 pairs them into one round: one side
sends `commitment_signed`, the peer answers with `revoke_and_ack`, and the next
round cannot start until that revocation has arrived
(`refs/bolts/02-peer-protocol.md:3097-3249`).  The layer below adds that
ordering as a *separate* relation over the same `Channel` record.

Both dance transitions are already legal `Step`s (`DanceStep.toStep`), so this
layer refines the lifecycle relation; it does not replace or weaken it.  It
also embeds into the wave-5 `UpdateStep` layer (`DanceStep.toUpdateStep` in
`LnLean.Proofs.Channel.CommitmentDanceTargets`), so every ledger and reserve
theorem about update traces applies unchanged.  Keeping the dance separate
leaves `ProtocolEvent`, `Step`, the executable `step?` scheduler, and every
balance/HTLC preservation theorem untouched.

The invariants (ordered round window, no stale commitment, revocation
monotonicity, balance/ledger preservation) are proved in
`LnLean.Proofs.Channel.CommitmentDanceTargets`. -/

/-- The two messages of one commitment round.  This event type is separate
from `ProtocolEvent` for the same reason as `UpdateEvent`: the executable
schedule model in `LnLean.Proofs.Liveness` matches `ProtocolEvent`
exhaustively. -/
inductive DanceEvent where
  | commitmentSigned
  | revokeAndAck
deriving Repr, DecidableEq, BEq

/-- The `ProtocolEvent` spelling of a dance event.  Both spellings already
exist in `ProtocolEvent`; the dance layer adds no message vocabulary. -/
def DanceEvent.toProtocolEvent : DanceEvent → ProtocolEvent
  | .commitmentSigned => ProtocolEvent.commitmentSigned
  | .revokeAndAck => ProtocolEvent.revokeAndAck

/-- The ordered round window.  `remoteCommitmentNumber` is either equal to the
local counter (no round in flight) or exactly one ahead (a `commitment_signed`
whose `revoke_and_ack` is still outstanding). -/
def DanceOrdered (c : Channel) : Prop :=
  c.localCommitmentNumber ≤ c.remoteCommitmentNumber ∧
    c.remoteCommitmentNumber ≤ c.localCommitmentNumber + 1

/-- The number of `commitment_signed` messages whose matching
`revoke_and_ack` is still outstanding. -/
def commitmentGap (c : Channel) : Nat :=
  c.remoteCommitmentNumber - c.localCommitmentNumber

/-- Commitment number `i` is revoked from the local viewpoint: it lies strictly
below the local commitment counter, so an earlier `revoke_and_ack` revealed its
per-commitment secret.  In an ordered state this watermark is at most the
remote commitment counter (`DanceOrdered`), which is why the same predicate
also rules out signing a stale remote commitment. -/
def CommitmentRevoked (c : Channel) (i : Nat) : Prop :=
  i < c.localCommitmentNumber

/-- Target of `commitment_signed`: advance the remote commitment counter.  The
balance, the HTLC list, the funding value, and the phase are unchanged. -/
def signRemoteCommitment (c : Channel) : Channel :=
  { c with remoteCommitmentNumber := c.remoteCommitmentNumber + 1 }

/-- Target of `revoke_and_ack`: advance the local commitment counter, which
revokes the previous local commitment.  The balance, the HTLC list, the funding
value, and the phase are unchanged. -/
def revokeLocalCommitment (c : Channel) : Channel :=
  { c with localCommitmentNumber := c.localCommitmentNumber + 1 }

/-- `DanceStep c e c'`: the ordered BOLT 2 commitment round.  Unlike the
lifecycle `Step`, the two messages alternate:

* `commitmentSigned` is legal only when no round is in flight
  (`remote = local`);
* `revokeAndAck` is legal only when exactly one signature is outstanding
  (`remote = local + 1`).

A state in which the local counter is ahead of the remote counter (which the
unguarded lifecycle relation permits) has no dance step. -/
inductive DanceStep : Channel → DanceEvent → Channel → Prop where
  /-- Sign the remote commitment, starting a round. -/
  | commitmentSigned (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hidle : c.remoteCommitmentNumber = c.localCommitmentNumber) :
      DanceStep c DanceEvent.commitmentSigned (signRemoteCommitment c)
  /-- Acknowledge and revoke the previous local commitment, closing the round. -/
  | revokeAndAck (c : Channel) (hphase : c.phase = ChannelPhase.normal)
      (hpending : c.remoteCommitmentNumber = c.localCommitmentNumber + 1) :
      DanceStep c DanceEvent.revokeAndAck (revokeLocalCommitment c)

/-- Every dance step is the corresponding unguarded lifecycle step: the dance
layer is a refinement of `Step`, not a second message semantics. -/
theorem DanceStep.toStep {c c' : Channel} {e : DanceEvent} (h : DanceStep c e c') :
    Step c e.toProtocolEvent c' := by
  cases h with
  | commitmentSigned hphase hidle =>
      simpa [DanceEvent.toProtocolEvent, signRemoteCommitment] using
        Step.commitmentSigned c hphase
  | revokeAndAck hphase hpending =>
      simpa [DanceEvent.toProtocolEvent, revokeLocalCommitment] using
        Step.revokeAndAck c hphase

/-- Reflexive-transitive closure of the ordered commitment round. -/
inductive DanceReachable : Channel → Channel → Prop where
  | refl (c : Channel) : DanceReachable c c
  | step {a b c : Channel} {e : DanceEvent} :
      DanceReachable a b → DanceStep b e c → DanceReachable a c

end LnLean.Channel
