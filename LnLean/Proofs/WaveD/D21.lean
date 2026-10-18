import LnLean.Protocol.Handshake
import LnLean.Protocol.Laws
import LnLean.Protocol.Messages
import LnLean.Protocol.Peer

/-!
# LnLean.Proofs.WaveD.D21

## English claim

BOLT 2 §"Message Retransmission" says that after a reconnection a node
re-sends the last `commitment_signed`, `revoke_and_ack`, `funding_signed`,
`channel_ready` and `shutdown` that the peer may not have seen, and that
`channel_reestablish` carries counters (`next_commitment_number`,
`next_revocation_number`) that let the peer detect what has to be replayed.
It must not roll the channel state back to an earlier commitment: the
counters and the retained retransmission copies describe the *current*
state.

This module proves, for the peer model in `LnLean.Protocol.Peer`:

* a successful `send` of a channel-directed, non-handshake message updates
  exactly the addressed channel by `ChannelRecord.recordSent`; hence for the
  retransmittable non-handshake kinds (`commitment_signed`,
  `revoke_and_ack`, `shutdown`) `resend` returns the very message that was
  sent (`waveD_d21_resend_after_send`);
* a successful `receive` updates exactly the addressed channel by
  `ChannelRecord.advanceReceived`; receiving a `channel_reestablish` is the
  identity on that channel (`waveD_d21_receive_reestablish_channel`), and in
  general no receive ever decreases the commitment or revocation counter,
  discards a retained retransmission copy, or breaks the BOLT 2 consistency
  condition `next_revocation_number ≤ next_commitment_number`
  (`waveD_d21_receive_no_rollback`);
* `send` routes every handshake message (including `funding_signed` and
  `channel_ready`) through `handshakeStep` and never through
  `ChannelRecord.recordSent`.  A concrete witness
  (`waveD_d21_handshake_retransmission_gap`) shows that a legal
  `funding_signed` send leaves no copy to resend, so the retransmission
  obligation for those two kinds is *not* met by the current model.

## BOLT sections

* BOLT 2 §"Message Retransmission"
  (`refs/bolts/02-peer-protocol.md:3357-3635`): the five retransmittable
  message kinds and the two `channel_reestablish` counters.
* BOLT 2 §"The `channel_reestablish` Message"
  (`refs/bolts/02-peer-protocol.md:3357-3405`, `:3451-3455`): counter
  meanings and the "never decrease" requirement.

## rust-lightning anchors (commit fe49009)

* `lightning/src/ln/channelmanager.rs:17831`: the reestablish handler that
  retransmits stored commitment messages.
* `lightning/src/ln/channel.rs:10826`: the inbound `channel_reestablish`
  path that compares the peer's counters against the local ones.
* `lightning/src/ln/channel.rs:13135`: `get_channel_reestablish` builds the
  outbound counters.

## What is NOT modelled

* There is no acknowledgement ledger.  `ChannelRecord` retains only the
  last message of each retransmittable kind, so "unacknowledged" cannot be
  distinguished from "already acknowledged"; the model proves the weaker,
  faithful property that the retained copy is the last sent one.
* `resend` is a pure query; the model has no scheduler or reconnection
  event that calls it.  `channel_reestablish` is modelled as an ordinary
  inbound message that advances no counters.
* No cryptographic claim: retained bytes are not authenticated here.
-/

namespace LnLean.Proofs.WaveD.D21

set_option autoImplicit false

open LnLean LnLean.Protocol

-- OBLIGATION: LN-WD-D21

/-! ## The retransmittable kinds -/

/-- The five message kinds BOLT 2 §"Message Retransmission" requires a node
to be able to retransmit after reconnection.  This is a decidable view of
the kinds handled by `ChannelRecord.lastSent` / `ChannelRecord.recordSent`. -/
def retransmittableKind : MsgKind → Bool
  | .fundingSigned => true
  | .channelReady => true
  | .commitmentSigned => true
  | .revokeAndAck => true
  | .shutdown => true
  | _ => false

@[simp] theorem retransmittable_commitmentSigned :
    retransmittableKind .commitmentSigned = true := rfl

@[simp] theorem retransmittable_revokeAndAck :
    retransmittableKind .revokeAndAck = true := rfl

@[simp] theorem retransmittable_shutdown :
    retransmittableKind .shutdown = true := rfl

/-! ## Structural lemmas about the channel record -/

/-- `recordSent` keeps the channel identifier. -/
theorem channelId_recordSent (c : ChannelRecord) (m : Msg) :
    (c.recordSent m).channelId = c.channelId := by
  cases m <;> rfl

/-- `advanceReceived` keeps the channel identifier. -/
theorem channelId_advanceReceived (c : ChannelRecord) (m : Msg) :
    (c.advanceReceived m).channelId = c.channelId := by
  cases m <;> simp only [ChannelRecord.advanceReceived, Msg.kind] <;>
    (try split) <;> rfl

/-- Recording a retransmittable message makes it the retained copy of its
own kind. -/
theorem lastSent_recordSent {c : ChannelRecord} {m : Msg}
    (h : retransmittableKind m.kind = true) :
    (c.recordSent m).lastSent m.kind = some m := by
  cases m <;>
    simp [retransmittableKind, ChannelRecord.recordSent, ChannelRecord.lastSent, Msg.kind] at h ⊢

/-- Receiving a message never discards a retained retransmission copy. -/
theorem lastSent_advanceReceived (c : ChannelRecord) (m : Msg) (k : MsgKind) :
    (c.advanceReceived m).lastSent k = c.lastSent k := by
  cases m <;> cases k <;>
    simp only [ChannelRecord.advanceReceived, ChannelRecord.lastSent, Msg.kind] <;>
    (try split) <;> rfl

/-- Receiving a message never decreases the commitment counter. -/
theorem advanceReceived_commitment_monotone (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextCommitmentNumber ≤
      (c.advanceReceived m).reestablish.nextCommitmentNumber := by
  cases m <;> simp only [ChannelRecord.advanceReceived, Msg.kind] <;>
    (try split) <;>
    simp [ReestablishFields.afterCommitment, ReestablishFields.afterRevocation] <;>
    omega

/-- Receiving a message never decreases the revocation counter. -/
theorem advanceReceived_revocation_monotone (c : ChannelRecord) (m : Msg) :
    c.reestablish.nextRevocationNumber ≤
      (c.advanceReceived m).reestablish.nextRevocationNumber := by
  cases m <;> simp only [ChannelRecord.advanceReceived, Msg.kind] <;>
    (try split) <;>
    simp [ReestablishFields.afterCommitment, ReestablishFields.afterRevocation] <;>
    omega

/-- Receiving a message preserves the BOLT 2 counter consistency condition. -/
theorem advanceReceived_consistent (c : ChannelRecord) (m : Msg)
    (h : c.reestablish.consistent) :
    (c.advanceReceived m).reestablish.consistent := by
  cases m <;> simp only [ChannelRecord.advanceReceived, Msg.kind] at h ⊢ <;>
    (try split) <;>
    simp [ReestablishFields.consistent, ReestablishFields.afterCommitment,
      ReestablishFields.afterRevocation] at h ⊢ <;>
    omega

/-! ## Locating a channel after `updateChannel` -/

/-- `List.find?` after a pointwise map: if the predicate is invariant under
the map, the found element is the image of the originally found element. -/
theorem find?_map_of_pred {α : Type} (l : List α) (p : α → Bool) (g : α → α)
    (hg : ∀ a, p (g a) = p a) :
    (l.map g).find? p = (l.find? p).map g := by
  rw [List.find?_map]
  have hcomp : (p ∘ g) = p := funext hg
  rw [hcomp]

/-- The predicate used by `findChannel` holds of the channel it returns. -/
theorem findChannel_pred (s : PeerState) (cid : ChannelId) (c : ChannelRecord)
    (h : findChannel s cid = some c) :
    (c.channelId == cid) = true := by
  unfold findChannel at h
  revert h
  induction s.channels with
  | nil => intro h; simp [List.find?] at h
  | cons a t ih =>
      intro h
      rw [List.find?_cons] at h
      split at h
      · rename_i hpred
        simp only [Option.some.injEq] at h
        subst h
        exact hpred
      · exact ih h

/-- `updateChannel` at the identifier of a known channel can be located
again, provided the update keeps the channel identifier's predicate true.
This is the bridge from the record-level laws to `resend`. -/
theorem findChannel_updateChannel_self (s : PeerState) (cid : ChannelId)
    (f : ChannelRecord → ChannelRecord) (c : ChannelRecord)
    (hfc : findChannel s cid = some c)
    (hf : ∀ a, (a.channelId == cid) = true → ((f a).channelId == cid) = true) :
    findChannel (updateChannel s cid f) cid = some (f c) := by
  have hpred : (c.channelId == cid) = true := findChannel_pred s cid c hfc
  have hmap := find?_map_of_pred s.channels (fun a => a.channelId == cid)
    (fun a => if (a.channelId == cid) = true then f a else a) (by
      intro a
      by_cases h : (a.channelId == cid) = true
      · simp [h, hf a h]
      · simp [h])
  have hfc' : s.channels.find? (fun a => a.channelId == cid) = some c := hfc
  simp only [findChannel, updateChannel] at hmap ⊢
  rw [hmap, hfc']
  simp [hpred]

/-! ## The peer transitions on the addressed channel -/

/-- A successful non-handshake channel-directed `send` updates exactly the
addressed channel, by `recordSent`. -/
theorem waveD_d21_send_channel_step (s s' : PeerState) (m out : Msg)
    (cid : ChannelId) (he : sendEvent? m = none) (hc : channelId? m = some cid)
    (c c' : ChannelRecord) (hfc : findChannel s cid = some c)
    (h : send s m = some (s', out))
    (hfc' : findChannel s' cid = some c') :
    c' = c.recordSent m := by
  unfold send at h
  cases ht : s.transport with
  | down => simp [ht] at h
  | up =>
      simp only [ht, he, hc] at h
      cases hf : findChannel s cid with
      | none => rw [hf] at h; simp at h
      | some c₀ =>
          rw [hf] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hc₀ : c₀ = c := by
            have h' := hfc
            rw [hf] at h'
            simpa using h'
          have hfind := findChannel_updateChannel_self s cid
            (fun ch => ch.recordSent m) c₀ hf (by
              intro a _ha
              rw [channelId_recordSent]
              exact _ha)
          rw [hfind] at hfc'
          have hc' : c' = c₀.recordSent m := by simpa using hfc'.symm
          rw [hc', hc₀]

/-- A successful non-handshake channel-directed `receive` updates exactly
the addressed channel, by `advanceReceived`. -/
theorem waveD_d21_receive_channel_step (s s' : PeerState) (m : Msg)
    (cid : ChannelId) (he : receiveEvent? m = none) (hc : channelId? m = some cid)
    (c c' : ChannelRecord) (hfc : findChannel s cid = some c)
    (h : receive s m = some s')
    (hfc' : findChannel s' cid = some c') :
    c' = c.advanceReceived m := by
  unfold receive at h
  cases ht : s.transport with
  | down => simp [ht] at h
  | up =>
      simp only [ht, he, hc] at h
      cases hf : findChannel s cid with
      | none => rw [hf] at h; simp at h
      | some c₀ =>
          rw [hf] at h
          simp only [Option.some.injEq] at h
          subst h
          have hc₀ : c₀ = c := by
            have h' := hfc
            rw [hf] at h'
            simpa using h'
          have hfind := findChannel_updateChannel_self s cid
            (fun _ => c₀.advanceReceived m) c₀ hf (by
              intro a _ha
              rw [channelId_advanceReceived]
              exact findChannel_pred s cid c₀ hf)
          rw [hfind] at hfc'
          have hc' : c' = c₀.advanceReceived m := by simpa using hfc'.symm
          rw [hc', hc₀]

/-! ## Main positive results -/

/-- **Retransmission.**  After a successful send of a retransmittable,
non-handshake channel message, `resend` returns exactly that message.  This
is the model's content of "re-send the last unacknowledged update". -/
theorem waveD_d21_resend_after_send (s s' : PeerState) (m out : Msg)
    (cid : ChannelId) (he : sendEvent? m = none) (hc : channelId? m = some cid)
    (c c' : ChannelRecord) (hfc : findChannel s cid = some c)
    (h : send s m = some (s', out))
    (hfc' : findChannel s' cid = some c')
    (hr : retransmittableKind m.kind = true) :
    resend s' cid m.kind = some m := by
  have hstep := waveD_d21_send_channel_step s s' m out cid he hc c c' hfc h hfc'
  rw [hstep] at hfc'
  rw [resend_of_channel s' cid m.kind (c.recordSent m) hfc']
  exact lastSent_recordSent hr

/-- **No rollback.**  A successful receive never decreases either
`channel_reestablish` counter of the addressed channel, never discards a
retained retransmission copy, and preserves the counter consistency
condition.  `channel_reestablish` itself therefore cannot roll the channel
back. -/
theorem waveD_d21_receive_no_rollback (s s' : PeerState) (m : Msg)
    (cid : ChannelId) (he : receiveEvent? m = none) (hc : channelId? m = some cid)
    (c c' : ChannelRecord) (hfc : findChannel s cid = some c)
    (h : receive s m = some s')
    (hfc' : findChannel s' cid = some c') :
    c.reestablish.nextCommitmentNumber ≤ c'.reestablish.nextCommitmentNumber ∧
    c.reestablish.nextRevocationNumber ≤ c'.reestablish.nextRevocationNumber ∧
    (∀ k : MsgKind, c'.lastSent k = c.lastSent k) ∧
    (c.reestablish.consistent → c'.reestablish.consistent) := by
  have hstep := waveD_d21_receive_channel_step s s' m cid he hc c c' hfc h hfc'
  subst hstep
  exact ⟨advanceReceived_commitment_monotone c m,
    advanceReceived_revocation_monotone c m,
    fun k => lastSent_advanceReceived c m k,
    fun hcons => advanceReceived_consistent c m hcons⟩

/-- Receiving a `channel_reestablish` for a known channel is the identity on
that channel: its counters and retained reestablish copies are unchanged.
This is the literal "reestablish does not roll state back" law. -/
theorem waveD_d21_receive_reestablish_channel (s s' : PeerState)
    (m : ChannelReestablish) (c c' : ChannelRecord)
    (hfc : findChannel s m.channelId = some c)
    (h : receive s (.channelReestablish m) = some s')
    (hfc' : findChannel s' m.channelId = some c') :
    c' = c := by
  have hstep := waveD_d21_receive_channel_step s s' (.channelReestablish m)
    m.channelId (by rfl) (by rfl) c c' hfc h hfc'
  simpa [ChannelRecord.advanceReceived, Msg.kind] using hstep

/-- **Retransmission after `channel_reestablish`.**  If a retransmittable
non-handshake update was sent and the peer then receives a
`channel_reestablish` for the same channel, `resend` still returns the
original update and the channel's counters were not rolled back.  This is
the composed form of the catalog claim. -/
theorem waveD_d21_reestablish_retransmits (s₀ s₁ s₂ : PeerState) (m out : Msg)
    (re : ChannelReestablish) (cid : ChannelId)
    (he : sendEvent? m = none) (hc : channelId? m = some cid)
    (c c₁ c₂ : ChannelRecord)
    (hfc : findChannel s₀ cid = some c)
    (hsend : send s₀ m = some (s₁, out))
    (hfc₁ : findChannel s₁ cid = some c₁)
    (hre : receive s₁ (.channelReestablish re) = some s₂)
    (hcid : re.channelId = cid)
    (hfc₂ : findChannel s₂ cid = some c₂)
    (hr : retransmittableKind m.kind = true) :
    resend s₂ cid m.kind = some m := by
  have hsent :=
    waveD_d21_resend_after_send s₀ s₁ m out cid he hc c c₁ hfc hsend hfc₁ hr
  have hfc₁' : findChannel s₁ re.channelId = some c₁ := by rw [hcid]; exact hfc₁
  have hfc₂' : findChannel s₂ re.channelId = some c₂ := by rw [hcid]; exact hfc₂
  have hidentity : c₂ = c₁ :=
    waveD_d21_receive_reestablish_channel s₁ s₂ re c₁ c₂ hfc₁' hre hfc₂'
  rw [resend_of_channel s₂ cid m.kind c₂ hfc₂, hidentity,
    ← resend_of_channel s₁ cid m.kind c₁ hfc₁]
  exact hsent

/-! ## The handshake retransmission gap -/

/-- `send` routes every handshake message through `handshakeStep`, and a
handshake send leaves the channel list untouched.  In particular it never
calls `ChannelRecord.recordSent`. -/
theorem waveD_d21_send_handshake_channels (s s' : PeerState) (m out : Msg)
    (e : HandshakeEvent) (he : sendEvent? m = some e)
    (h : send s m = some (s', out)) :
    s'.channels = s.channels := by
  unfold send at h
  cases ht : s.transport with
  | down => simp [ht] at h
  | up =>
      simp only [ht, he] at h
      cases hstep : handshakeStep s.handshake e with
      | none => rw [hstep] at h; simp at h
      | some hs =>
          rw [hstep] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl

/-- Consequently a handshake send does not change what `resend` returns. -/
theorem waveD_d21_resend_unchanged_by_handshake_send (s s' : PeerState)
    (m out : Msg) (e : HandshakeEvent) (he : sendEvent? m = some e)
    (h : send s m = some (s', out)) (cid : ChannelId) (kind : MsgKind) :
    resend s' cid kind = resend s cid kind := by
  have hch := waveD_d21_send_handshake_channels s s' m out e he h
  unfold resend findChannel
  rw [hch]

/-- A concrete `funding_signed` message for the zero channel id. -/
def demoFundingSigned : Msg :=
  .fundingSigned { channelId := ChannelId.zero, signature := ⟨ByteArray.empty⟩ }

/-- A handshake state in which `funding_signed` may be sent: `init` has been
exchanged and `funding_created` has been received. -/
def demoHandshake : HandshakeState :=
  { initSent := true, initReceived := true, fundingCreatedReceived := true }

/-- A peer with the transport up, that handshake state, and one channel
whose retained `funding_signed` slot is empty. -/
def demoPeer : PeerState :=
  { identity := { bytes := ByteArray.mk ((List.replicate 33 (0 : UInt8)).toArray) }
    transport := .up
    handshake := demoHandshake
    channels := [{ channelId := ChannelId.zero, reestablish := ReestablishFields.initial }] }

/-- The zero channel id denotes the demo peer's only channel. -/
theorem waveD_d21_demo_findChannel :
    findChannel demoPeer ChannelId.zero =
      some { channelId := ChannelId.zero, reestablish := ReestablishFields.initial } := by
  simp [findChannel, demoPeer]
  decide

/-- **Negative result.**  The model's `send` does not retain `funding_signed`
(or `channel_ready`): both are handshake messages and take the
`handshakeStep` branch before `ChannelRecord.recordSent` is reached.  There
is therefore a peer state in which a legal `funding_signed` send leaves
`resend` with no copy to return (the state is built directly; no
reachability-from-`initial` claim is made, since the model has no
reconnection event). -/
theorem waveD_d21_handshake_retransmission_gap :
    ∃ (s s' : PeerState) (out : Msg),
      send s demoFundingSigned = some (s', out) ∧
      resend s' ChannelId.zero .fundingSigned = none := by
  have hsome : (send demoPeer demoFundingSigned).isSome = true := by decide
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨demoPeer, p.1, p.2, hp, ?_⟩
  rw [waveD_d21_resend_unchanged_by_handshake_send demoPeer p.1
    demoFundingSigned p.2 .sendFundingSigned (by rfl) hp ChannelId.zero .fundingSigned]
  simp [resend, waveD_d21_demo_findChannel, ChannelRecord.lastSent]

end LnLean.Proofs.WaveD.D21
