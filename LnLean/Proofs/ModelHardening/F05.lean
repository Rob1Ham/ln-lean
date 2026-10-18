import LnLean.Routing.Gossip
import LnLean.Routing.Laws
import LnLean.Proofs.Routing.GossipProps

/-!
# LnLean.Proofs.ModelHardening.F05 — gossip announced-key admission

English claim of this module:

* `UpdateKeyAnnounced s u` is the missing BOLT 7 admission predicate: the
  `signingKey` of a `channel_update` must be one of the two `node_id` keys
  carried by a `channel_announcement` for the same `short_channel_id`.
* `admitChannelUpdate` is the corresponding store step.  It accepts an
  update only when the key predicate holds **and** the update's abstract
  signature verifies, and then applies the wave-A timestamp replacement
  rule.  Thus every accepted update has an announced signing key, and the
  key remains announced in the resulting store.
* The un-gated wave-A step `acceptChannelUpdate` is shown to be unsound for
  the same claim by an explicit counterexample: an empty store, an
  always-accepting verifier, and an update whose key was never announced.
  The refuted unconditional statement has been removed; the admitted-step
  soundness theorem `admitChannelUpdate_change_key_announced_after` is the
  strongest true replacement that the current model supports.

BOLT 7 anchor:

* `refs/bolts/07-routing-gossip.md:544` — a `channel_update` is signed by
  the `node_id` of the forwarding node, which is the `node_id_1` or
  `node_id_2` from the matching `channel_announcement`.  Wave A's
  `ChannelUpdate.signingKey` is an independent field and the store never
  looks it up in `GossipState.announcements`.

What is **not** modelled:

* Which of the two announced keys is the correct one for a direction.
  `channel_flags` bit 0 is the BOLT 7 direction bit, but wave A does not
  decode it in this module, so `UpdateKeyAnnounced` accepts either key.
  The direction-keyed refinement is recorded in the report.
* The link between `ChannelAnnellation.node1 : NodeId` and
  `ChannelAnnellation.nodeKey1 : PubKey`; only the two announcement keys are
  compared with the update key.
* Cryptographic unforgeability.  `SigVerifier` is an abstract function and
  this module proves only the conditional admission bridge.
-/

namespace LnLean.Proofs.ModelHardening.F05

open LnLean.Routing
open LnLean.Routing.GossipProps
open Classical

set_option autoImplicit false

/-! ## The announced-key admission predicate -/

/-- The missing BOLT 7 key-attribution predicate: some stored
`channel_announcement` for the update's `short_channel_id` announces the
update's `signingKey` as `node_id_1` or `node_id_2`.

This is deliberately a proposition over the *current* store.  It does not
assert that the announcement itself passed `signaturesValid`; that check is
already part of the checked announcement path (`applyGossipChecked`) and is
layered on top in `UpdateKeyAdmissible` below. -/
def UpdateKeyAnnounced (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)

/-- The stronger admission predicate that also requires the backing
announcement to carry the four valid BOLT 7 signatures. -/
def UpdateKeyAdmissible (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.signaturesValid verify ∧
    a.shortChannelId = u.shortChannelId ∧
    (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)

/-- The stronger predicate entails the key-only one. -/
theorem updateKeyAdmissible_implies_announced (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) (h : UpdateKeyAdmissible verify s u) :
    UpdateKeyAnnounced s u := by
  rcases h with ⟨a, ha, _, hscid, hkey⟩
  exact ⟨a, ha, hscid, hkey⟩

/-! ## Admission and its soundness -/

/-- Accept a `channel_update` only when its signing key was announced for
the same channel and its abstract signature verifies; then apply the wave-A
timestamp rule.  This is the key-admission bridge missing from wave A. -/
noncomputable def admitChannelUpdate (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) : GossipState :=
  if UpdateKeyAnnounced s u ∧ u.signatureValid verify then
    s.applyUpdate u
  else s

/-- An update with no announced key is rejected outright. -/
theorem admitChannelUpdate_rejects_unannounced (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) (h : ¬ UpdateKeyAnnounced s u) :
    admitChannelUpdate verify s u = s := by
  unfold admitChannelUpdate
  rw [ite_eq_right]
  rintro ⟨hk, _⟩
  exact h hk

/-- **Key soundness.**  Any change made by the admitted step requires an
announced signing key. -/
theorem admitChannelUpdate_change_requires_key (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitChannelUpdate verify s u ≠ s) :
    UpdateKeyAnnounced s u := by
  apply Classical.byContradiction
  intro hk
  exact h (admitChannelUpdate_rejects_unannounced verify s u hk)

/-- **Signature soundness.**  Any change made by the admitted step also
requires the abstract signature predicate. -/
theorem admitChannelUpdate_change_requires_signature (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitChannelUpdate verify s u ≠ s) :
    u.signatureValid verify := by
  apply Classical.byContradiction
  intro hsig
  apply h
  unfold admitChannelUpdate
  rw [ite_eq_right]
  rintro ⟨_, hs⟩
  exact hsig hs

/-- **Timestamp soundness.**  Any change made by the admitted step also
requires a strictly newer timestamp. -/
theorem admitChannelUpdate_change_requires_newer (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitChannelUpdate verify s u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  by_cases hnew : s.latestUpdateTimestamp < u.timestamp
  · exact hnew
  · have hle : u.timestamp ≤ s.latestUpdateTimestamp := Nat.le_of_not_lt hnew
    have heq : admitChannelUpdate verify s u = s := by
      unfold admitChannelUpdate
      split
      · exact GossipState.applyUpdate_stale s u hle
      · rfl
    exact absurd heq h

/-- **Full soundness of announced-key admission.**  Every accepted update
has an announced key, a verifying signature, and a strictly newer
timestamp. -/
theorem admitChannelUpdate_sound (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) (h : admitChannelUpdate verify s u ≠ s) :
    UpdateKeyAnnounced s u ∧ u.signatureValid verify ∧
      s.latestUpdateTimestamp < u.timestamp :=
  ⟨admitChannelUpdate_change_requires_key verify s u h,
   admitChannelUpdate_change_requires_signature verify s u h,
   admitChannelUpdate_change_requires_newer verify s u h⟩

/-- The converse: an update that satisfies all three admission conditions
really changes the store. -/
theorem admitChannelUpdate_changes_of_conditions (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (hk : UpdateKeyAnnounced s u) (hsig : u.signatureValid verify)
    (hnew : s.latestUpdateTimestamp < u.timestamp) :
    admitChannelUpdate verify s u ≠ s := by
  intro heq
  have hupd : (admitChannelUpdate verify s u).updates = s.updates :=
    congrArg GossipState.updates heq
  have hnewupd : (admitChannelUpdate verify s u).updates = u :: s.updates := by
    unfold admitChannelUpdate
    rw [ite_eq_left ⟨hk, hsig⟩]
    exact GossipState.applyUpdate_new s u hnew
  rw [hnewupd] at hupd
  have hlen := congrArg List.length hupd
  simp only [List.length_cons] at hlen
  omega

/-- **Exact characterization.**  The admitted step changes the store iff
the key is announced, the signature verifies, and the timestamp is strictly
newer. -/
theorem admitChannelUpdate_change_iff (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) :
    admitChannelUpdate verify s u ≠ s ↔
      (UpdateKeyAnnounced s u ∧ u.signatureValid verify ∧
        s.latestUpdateTimestamp < u.timestamp) := by
  constructor
  · intro h
    exact admitChannelUpdate_sound verify s u h
  · rintro ⟨hk, hsig, hnew⟩
    exact admitChannelUpdate_changes_of_conditions verify s u hk hsig hnew

/-- The admitted step stores an accepted update at the head of the update
list, exactly as wave A does once its guard passes. -/
theorem admitChannelUpdate_updates_of_change (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitChannelUpdate verify s u ≠ s) :
    (admitChannelUpdate verify s u).updates = u :: s.updates := by
  rcases admitChannelUpdate_sound verify s u h with ⟨hk, hsig, hnew⟩
  unfold admitChannelUpdate
  rw [ite_eq_left ⟨hk, hsig⟩]
  exact GossipState.applyUpdate_new s u hnew

/-- If the key is already announced, the admitted step is exactly wave A's
signature-checked step; the key check is the only extra gate. -/
theorem admitChannelUpdate_eq_acceptChannelUpdate_of_announced
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (hk : UpdateKeyAnnounced s u) :
    admitChannelUpdate verify s u = acceptChannelUpdate verify s u := by
  unfold admitChannelUpdate acceptChannelUpdate
  by_cases hsig : u.signatureValid verify
  · rw [ite_eq_left ⟨hk, hsig⟩, ite_eq_left hsig]
  · rw [ite_eq_right (fun h => hsig h.2), ite_eq_right hsig]

/-! ## The key survives the accepted step -/

/-- `admitChannelUpdate` never changes the announcement list. -/
theorem admitChannelUpdate_announcements (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) :
    (admitChannelUpdate verify s u).announcements = s.announcements := by
  unfold admitChannelUpdate
  split
  · exact GossipProps.applyUpdate_announcements s u
  · rfl

/-- An announced key remains announced after the admitted step, so the
post-state predicate holds with the same witness announcement. -/
theorem updateKeyAnnounced_admitChannelUpdate (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) (h : UpdateKeyAnnounced s u) :
    UpdateKeyAnnounced (admitChannelUpdate verify s u) u := by
  rcases h with ⟨a, ha, hscid, hkey⟩
  refine ⟨a, ?_, hscid, hkey⟩
  unfold admitChannelUpdate
  split
  · unfold GossipState.applyUpdate
    split <;> simpa using ha
  · exact ha

/-- **Post-state form of key soundness.**  Every accepted update has an
announced signing key both before and after the store step. -/
theorem admitChannelUpdate_change_key_announced_after (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate)
    (h : admitChannelUpdate verify s u ≠ s) :
    UpdateKeyAnnounced (admitChannelUpdate verify s u) u :=
  updateKeyAnnounced_admitChannelUpdate verify s u
    (admitChannelUpdate_change_requires_key verify s u h)

/-! ## The unannounced-key counterexample -/

private def f05EmptySig : GossipSignature := ⟨ByteArray.empty⟩

private def f05ZeroKey : PubKey := ⟨ByteArray.empty⟩

private def f05ZeroScid : ShortChannelId := ⟨0, 0, 0⟩

/-- A verifier that accepts every signature.  Used only to expose the
missing key admission; it is not an unforgeability assumption. -/
private def f05AcceptAll : SigVerifier := fun _ _ _ => true

private def f05EmptyState : GossipState := ⟨[], [], []⟩

private def f05UnannouncedUpdate : ChannelUpdate :=
  { shortChannelId := f05ZeroScid
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := f05ZeroKey
    digest := ByteArray.empty
    signature := f05EmptySig }

/-- The un-gated wave-A step really accepts the unannounced-key update. -/
private theorem f05_acceptAll_update_changes :
    acceptChannelUpdate f05AcceptAll f05EmptyState f05UnannouncedUpdate ≠
      f05EmptyState := by
  intro h
  have hu := congrArg GossipState.updates h
  simp [acceptChannelUpdate, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, f05EmptyState,
    f05UnannouncedUpdate, ChannelUpdate.signatureValid, signatureValid,
    f05AcceptAll] at hu

/-- **The unannounced-key counterexample to the faithful unconditional
statement.**  With an always-accepting verifier, an empty store, and an
update carrying an empty key, `acceptChannelUpdate` changes the store while
no announcement can supply the key. -/
theorem waveF_f05_unannounced_key_counterexample :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      acceptChannelUpdate verify s u ≠ s ∧ ¬ UpdateKeyAnnounced s u := by
  refine ⟨f05AcceptAll, f05EmptyState, f05UnannouncedUpdate,
    f05_acceptAll_update_changes, ?_⟩
  rintro ⟨a, ha, _⟩
  simp [f05EmptyState] at ha

/-- The same update is rejected by the announced-key admission step. -/
theorem waveF_f05_admission_rejects_unannounced_key :
    admitChannelUpdate f05AcceptAll f05EmptyState f05UnannouncedUpdate =
      f05EmptyState := by
  apply admitChannelUpdate_rejects_unannounced
  rintro ⟨a, ha, _⟩
  simp [f05EmptyState] at ha

/-! ## The refuted unconditional claim

The unconditional statement is false for wave A, as
`waveF_f05_unannounced_key_counterexample` shows.  It has been removed rather
than kept as an open site; the admitted step `admitChannelUpdate` and its
soundness theorems above are the strongest true replacement. -/

-- REPAIRED: removed the false unconditional
-- `waveF_f05_accepted_update_key_announced` (counterexample:
-- `waveF_f05_unannounced_key_counterexample`).  Strongest true replacement:
-- `admitChannelUpdate_change_key_announced_after`, with the admitted step
-- `admitChannelUpdate` and its full soundness `admitChannelUpdate_sound`.

end LnLean.Proofs.ModelHardening.F05
