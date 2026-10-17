import LnLean.Channel.Types

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

rust-lightning anchors at `fe4900930c6bd5786ec4203274d7cf312776a5a6`.
* `lightning/src/ln/channel.rs:799` (`enum ChannelState`), `:1552`
  (`enum ChannelPhase`), `:725-731` (the two shutdown flags),
  `:773-776` (`AwaitingRemoteRevoke` lock on a second `commitment_signed`).
* `lightning/src/ln/channelmanager.rs` is the message dispatcher; the
  individual handlers are in `channel.rs` (for example
  `funding_signed`/`funding_created` handling around `channel.rs:1552-1700`).

What is NOT modelled.
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

end LnLean.Channel
