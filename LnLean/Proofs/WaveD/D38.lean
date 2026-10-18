import LnLean.Routing.Gossip
import LnLean.Routing.Laws
import LnLean.Proofs.Routing.GossipProps

/-!
# D38 — Gossip signing-key admission

Catalog obligation `LN-GOSSIP-001`; BOLT 7, "The `channel_update` Message"
(`refs/bolts/07-routing-gossip.md:544`): the `node_id` used to verify a
`channel_update` signature is determined by the matching
`channel_announcement`, not chosen by the update itself.

Wave-A `ChannelUpdate` carries an independent `signingKey : PubKey` field and
`SigVerifier` is an arbitrary function, so `acceptChannelUpdate` accepts an
update whose signing key was never announced for its `short_channel_id`.
The unconditional attribution claim is therefore false in this model (a
concrete counterexample is mechanised below).  This module supplies the
missing admission layer:

* `announcedKeyAdmitted s u` — the reusable BOLT 7 admission predicate: the
  update's signing key is one of the two node keys announced for the same
  `short_channel_id`.
* `channelUpdateAdmission verify s u` — signature verification *and*
  announced-key admission.
* `applyUpdateIfAdmitted Admission s u` — a generic admission-gated store
  step, with its soundness lemmas.
* `acceptChannelUpdateAnnounced verify s u` — the BOLT 7 instantiation.

The main conditional theorem,
`waveD_d38_accepted_update_signing_key_announced`, says that every change
made by `acceptChannelUpdateAnnounced` entails signing-key attribution: there
is a stored announcement for the channel naming the update's signing key.
No cryptographic unforgeability is claimed; the verifier remains an abstract
parameter (assumptions C3/C4 in `docs/ASSUMPTIONS.md`).

The counterexample `waveD_d38_unannounced_key_counterexample` uses an
always-accepting verifier and a store that *does* contain an announcement for
the channel, but with two different node keys.  The wave-A acceptance path
still stores the update, and the key is not announced, so the obligation
cannot be closed without the admission check implemented here.

Every theorem is proved without `sorry`, `axiom`, `admit`, `native_decide`,
`unsafe`, or `@[implemented_by]`.  No new dependency is introduced.
-/

namespace LnLean.Proofs.WaveD.D38

set_option autoImplicit false

open LnLean.Routing
open LnLean.Routing.GossipProps
open Classical

-- OBLIGATION: LN-WD-D38

/-! ## The announced-key admission predicate -/

/-- **BOLT 7 announced-key admission.**  A `channel_update` for
`u.shortChannelId` may be attributed to `u.signingKey` only when a stored
`channel_announcement` for the same `short_channel_id` names that key as one
of its two `node_id`s.

This is the reusable admission predicate missing from wave A.  It is
`Prop`-valued (no decidability requirement is imposed on callers); the gated
store step below decides it classically. -/
def announcedKeyAdmitted (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)

/-- The predicate is exactly the attribution condition isolated by the
routing proof layer, which makes the two formulations interchangeable. -/
theorem waveD_d38_announcedKeyAdmitted_iff_updateKeyAnnounced
    (s : GossipState) (u : ChannelUpdate) :
    announcedKeyAdmitted s u ↔ updateKeyAnnounced s u :=
  Iff.rfl

/-- The admission predicate is invariant under `applyUpdate`: accepting an
update only consults the announcement list, which is never modified. -/
theorem waveD_d38_announcedKeyAdmitted_applyUpdate (s : GossipState)
    (u v : ChannelUpdate) (h : announcedKeyAdmitted s v) :
    announcedKeyAdmitted (s.applyUpdate u) v := by
  rcases h with ⟨a, ha, hscid, hkey⟩
  refine ⟨a, ?_, hscid, hkey⟩
  unfold GossipState.applyUpdate
  split <;> simpa using ha

/-! ## Admission-gated store application -/

/-- A generic admission-gated update: the store changes only when `Admission`
holds.  This is the reusable seam into which a BOLT 7 admission predicate
(announced key, signature length, chain check, ...) is plugged. -/
noncomputable def applyUpdateIfAdmitted
    (Admission : GossipState → ChannelUpdate → Prop)
    (s : GossipState) (u : ChannelUpdate) : GossipState :=
  if Admission s u then s.applyUpdate u else s

/-- An admitted update is applied by the wave-A timestamp rule. -/
theorem waveD_d38_applyUpdateIfAdmitted_eq_of_admission
    (Admission : GossipState → ChannelUpdate → Prop)
    (s : GossipState) (u : ChannelUpdate) (h : Admission s u) :
    applyUpdateIfAdmitted Admission s u = s.applyUpdate u := by
  unfold applyUpdateIfAdmitted
  rw [ite_eq_left h]

/-- A rejected update is a no-op. -/
theorem waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
    (Admission : GossipState → ChannelUpdate → Prop)
    (s : GossipState) (u : ChannelUpdate) (h : ¬ Admission s u) :
    applyUpdateIfAdmitted Admission s u = s := by
  unfold applyUpdateIfAdmitted
  rw [ite_eq_right h]

/-- **Generic gate soundness.**  Every change made by an admission-gated step
entails the admission predicate. -/
theorem waveD_d38_applyUpdateIfAdmitted_change_requires_admission
    (Admission : GossipState → ChannelUpdate → Prop)
    (s : GossipState) (u : ChannelUpdate)
    (h : applyUpdateIfAdmitted Admission s u ≠ s) : Admission s u := by
  apply Classical.byContradiction
  intro hnot
  exact h (waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
    Admission s u hnot)

/-- The BOLT 7 admission predicate for a `channel_update`: the signature
verifies under the update's own key **and** that key is announced for the
update's channel. -/
def channelUpdateAdmission (verify : SigVerifier) (s : GossipState)
    (u : ChannelUpdate) : Prop :=
  u.signatureValid verify ∧ announcedKeyAdmitted s u

/-- The BOLT 7 instantiation of the generic gate.  This is the store-level
`channel_update` path that closes the wave-A admission gap. -/
noncomputable def acceptChannelUpdateAnnounced (verify : SigVerifier)
    (s : GossipState) (u : ChannelUpdate) : GossipState :=
  applyUpdateIfAdmitted (channelUpdateAdmission verify) s u

/-- An update with an announced key is applied exactly as in wave A (the
signature gate is shared); the admission layer only rejects unannounced
keys. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_eq_acceptChannelUpdate
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : announcedKeyAdmitted s u) :
    acceptChannelUpdateAnnounced verify s u =
      acceptChannelUpdate verify s u := by
  by_cases hsig : u.signatureValid verify
  · rw [acceptChannelUpdateAnnounced,
      waveD_d38_applyUpdateIfAdmitted_eq_of_admission
        (channelUpdateAdmission verify) s u ⟨hsig, h⟩]
    unfold acceptChannelUpdate
    rw [ite_eq_left hsig]
  · rw [acceptChannelUpdateAnnounced,
      waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
        (channelUpdateAdmission verify) s u (fun hc => hsig hc.1)]
    unfold acceptChannelUpdate
    rw [ite_eq_right hsig]

/-- With both admission components, the gated step is exactly the wave-A
`GossipState.applyUpdate`. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_apply
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (hsig : u.signatureValid verify) (hkey : announcedKeyAdmitted s u) :
    acceptChannelUpdateAnnounced verify s u = s.applyUpdate u :=
  waveD_d38_applyUpdateIfAdmitted_eq_of_admission
    (channelUpdateAdmission verify) s u ⟨hsig, hkey⟩

/-- An update whose key is not announced is rejected outright. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_rejects_unannounced
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : ¬ announcedKeyAdmitted s u) :
    acceptChannelUpdateAnnounced verify s u = s := by
  apply waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
  intro hc
  exact h hc.2

/-- An update whose signature does not verify is rejected outright. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_rejects_invalid
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : ¬ u.signatureValid verify) :
    acceptChannelUpdateAnnounced verify s u = s := by
  apply waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
  intro hc
  exact h hc.1

/-! ## Conditional signing-key attribution -/

/-- **Admission soundness.**  Any change made by the announced-key-gated step
requires both a verifying signature and an announced signing key. -/
theorem waveD_d38_announcedKeyAdmission_change_requires_admission
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    u.signatureValid verify ∧ announcedKeyAdmitted s u :=
  waveD_d38_applyUpdateIfAdmitted_change_requires_admission
    (channelUpdateAdmission verify) s u h

/-- **Conditional `LN-GOSSIP-001`.**  Under announced-key admission, every
accepted `channel_update` is signed by one of the two node keys announced for
its `short_channel_id`.

The conclusion is exactly the attribution property that wave-A
`acceptChannelUpdate` does not establish; the added hypothesis is not an
extra assumption but the admission check implemented by
`acceptChannelUpdateAnnounced`. -/
theorem waveD_d38_accepted_update_signing_key_announced
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
      (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey) :=
  (waveD_d38_announcedKeyAdmission_change_requires_admission
    verify s u h).2

/-- The attribution theorem in the routing layer's predicate form. -/
theorem waveD_d38_accepted_update_updateKeyAnnounced
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    updateKeyAnnounced s u :=
  (waveD_d38_announcedKeyAdmitted_iff_updateKeyAnnounced s u).mp
    (waveD_d38_accepted_update_signing_key_announced verify s u h)

/-- An accepted update's signature verifies under the update's signing key. -/
theorem waveD_d38_accepted_update_signature_valid
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    u.signatureValid verify :=
  (waveD_d38_announcedKeyAdmission_change_requires_admission
    verify s u h).1

/-- An accepted update carries a strictly newer timestamp than the store's
clock. -/
theorem waveD_d38_accepted_update_newer
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  have hAdm := waveD_d38_announcedKeyAdmission_change_requires_admission
    verify s u h
  rw [waveD_d38_acceptChannelUpdateAnnounced_eq_acceptChannelUpdate
    verify s u hAdm.2] at h
  exact acceptChannelUpdate_change_requires_newer verify s u h

/-- Bundled admission soundness: signature, attribution, and freshness. -/
theorem waveD_d38_accepted_update_sound
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (h : acceptChannelUpdateAnnounced verify s u ≠ s) :
    u.signatureValid verify ∧
      (∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey)) ∧
      s.latestUpdateTimestamp < u.timestamp :=
  ⟨waveD_d38_accepted_update_signature_valid verify s u h,
   waveD_d38_accepted_update_signing_key_announced verify s u h,
   waveD_d38_accepted_update_newer verify s u h⟩

/-- Announced-key admission survives any gated `channel_update` step. -/
theorem waveD_d38_announcedKeyAdmitted_acceptChannelUpdateAnnounced
    (verify : SigVerifier) (s : GossipState) (u v : ChannelUpdate)
    (h : announcedKeyAdmitted s v) :
    announcedKeyAdmitted (acceptChannelUpdateAnnounced verify s u) v := by
  by_cases hadm : channelUpdateAdmission verify s u
  · rw [acceptChannelUpdateAnnounced,
      waveD_d38_applyUpdateIfAdmitted_eq_of_admission
        (channelUpdateAdmission verify) s u hadm]
    exact waveD_d38_announcedKeyAdmitted_applyUpdate s u v h
  · rw [acceptChannelUpdateAnnounced,
      waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
        (channelUpdateAdmission verify) s u hadm]
    exact h

/-- A valid but stale update is a no-op even after admission. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_stale
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate)
    (hsig : u.signatureValid verify) (hkey : announcedKeyAdmitted s u)
    (h : u.timestamp ≤ s.latestUpdateTimestamp) :
    acceptChannelUpdateAnnounced verify s u = s := by
  rw [waveD_d38_acceptChannelUpdateAnnounced_apply verify s u hsig hkey]
  exact GossipState.applyUpdate_stale s u h

/-- Admission-gated application is idempotent: a second delivery of the same
update is stale, so the store is unchanged. -/
theorem waveD_d38_acceptChannelUpdateAnnounced_idempotent
    (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate) :
    acceptChannelUpdateAnnounced verify
        (acceptChannelUpdateAnnounced verify s u) u =
      acceptChannelUpdateAnnounced verify s u := by
  by_cases hadm : channelUpdateAdmission verify s u
  · have hstate : acceptChannelUpdateAnnounced verify s u = s.applyUpdate u :=
      waveD_d38_applyUpdateIfAdmitted_eq_of_admission
        (channelUpdateAdmission verify) s u hadm
    rw [hstate]
    have hadm' : channelUpdateAdmission verify (s.applyUpdate u) u :=
      ⟨hadm.1, waveD_d38_announcedKeyAdmitted_applyUpdate s u u hadm.2⟩
    unfold acceptChannelUpdateAnnounced
    rw [waveD_d38_applyUpdateIfAdmitted_eq_of_admission
      (channelUpdateAdmission verify) (s.applyUpdate u) u hadm']
    exact gossip_applyUpdate_idempotent s u
  · unfold acceptChannelUpdateAnnounced
    rw [waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
      (channelUpdateAdmission verify) s u hadm]
    exact waveD_d38_applyUpdateIfAdmitted_eq_of_not_admission
      (channelUpdateAdmission verify) s u hadm

/-! ## The unannounced-key counterexample -/

/-- A verifier that accepts every signature; it is used only to expose the
wave-A admission gap. -/
private def d38AcceptAll : SigVerifier := fun _ _ _ => true

/-- The empty-byte key used for the first announced node key. -/
private def d38KeyA : PubKey := ⟨ByteArray.empty⟩

/-- The second announced node key: a one-byte key, distinct from `d38KeyA`. -/
private def d38KeyB : PubKey := ⟨ByteArray.mk #[0]⟩

/-- A two-byte key that is not among the announced keys. -/
private def d38UnannouncedKey : PubKey := ⟨ByteArray.mk #[0, 0]⟩

/-- The empty key differs from the two-byte key, by byte length. -/
private theorem d38_keyA_ne_unannounced :
    d38KeyA ≠ d38UnannouncedKey := by
  intro h
  have hs : d38KeyA.bytes.size = d38UnannouncedKey.bytes.size :=
    congrArg (fun k : PubKey => k.bytes.size) h
  have h0 : d38KeyA.bytes.size = 0 := rfl
  have h2 : d38UnannouncedKey.bytes.size = 2 := rfl
  rw [h0, h2] at hs
  omega

/-- The one-byte announced key differs from the two-byte key. -/
private theorem d38_keyB_ne_unannounced :
    d38KeyB ≠ d38UnannouncedKey := by
  intro h
  have hs : d38KeyB.bytes.size = d38UnannouncedKey.bytes.size :=
    congrArg (fun k : PubKey => k.bytes.size) h
  have h1 : d38KeyB.bytes.size = 1 := rfl
  have h2 : d38UnannouncedKey.bytes.size = 2 := rfl
  rw [h1, h2] at hs
  omega

/-- The channel identifier shared by the announcement and the update. -/
private def d38Scid : ShortChannelId := ⟨1, 2, 3⟩

/-- A genuine `channel_announcement` binding `d38Scid` to `d38KeyA` and
`d38KeyB`.  All four signatures are empty, which the always-accepting
verifier accepts. -/
private def d38Announcement : ChannelAnnellation :=
  { shortChannelId := d38Scid
    node1 := ⟨1⟩
    node2 := ⟨2⟩
    nodeKey1 := d38KeyA
    nodeKey2 := d38KeyB
    bitcoinKey1 := d38KeyA
    bitcoinKey2 := d38KeyB
    capacitySat := 1000
    digest := ByteArray.empty
    nodeSignature1 := ⟨ByteArray.empty⟩
    nodeSignature2 := ⟨ByteArray.empty⟩
    bitcoinSignature1 := ⟨ByteArray.empty⟩
    bitcoinSignature2 := ⟨ByteArray.empty⟩ }

/-- A store that has the announcement for `d38Scid` but no updates yet. -/
private def d38Store : GossipState :=
  { announcements := [d38Announcement]
    updates := []
    nodeAnnouncements := [] }

/-- A strictly newer update for the announced channel whose signing key is
`d38UnannouncedKey`, which is neither announced node key. -/
private def d38Update : ChannelUpdate :=
  { shortChannelId := d38Scid
    timestamp := 1
    messageFlags := 0
    channelFlags := 0
    cltvDelta := 1
    htlcMinimumMsat := Msat.zero
    feeBaseMsat := Msat.zero
    feeProportionalMillionths := 0
    htlcMaximumMsat := Msat.MAX
    signingKey := d38UnannouncedKey
    digest := ByteArray.empty
    signature := ⟨ByteArray.empty⟩ }

/-- The update really changes the store under the wave-A path. -/
private theorem d38_acceptAll_update_changes :
    acceptChannelUpdate d38AcceptAll d38Store d38Update ≠ d38Store := by
  intro h
  have hu := congrArg GossipState.updates h
  simp [acceptChannelUpdate, GossipState.applyUpdate,
    GossipState.latestUpdateTimestamp, latestTimestamp, d38Store, d38Update,
    ChannelUpdate.signatureValid, signatureValid, d38AcceptAll] at hu

/-- The update's key is not announced for its channel. -/
private theorem d38_update_key_not_announced :
    ¬ announcedKeyAdmitted d38Store d38Update := by
  rintro ⟨a, ha, _hscid, hkey⟩
  simp only [d38Store, List.mem_cons, List.mem_nil_iff, or_false] at ha
  subst a
  rcases hkey with h1 | h2
  · exact d38_keyA_ne_unannounced h1
  · exact d38_keyB_ne_unannounced h2

/-- **Counterexample to the unconditional `LN-GOSSIP-001`.**

There are a verifier, a store that contains an announcement for the update's
channel, and an accepted update whose signing key is neither of the two
announced node keys.  The wave-A `acceptChannelUpdate` still stores the
update, so signing-key attribution cannot hold without the admission check
`announcedKeyAdmitted`. -/
theorem waveD_d38_unannounced_key_counterexample :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      (∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId) ∧
      acceptChannelUpdate verify s u ≠ s ∧
      ¬ announcedKeyAdmitted s u := by
  refine ⟨d38AcceptAll, d38Store, d38Update,
    ⟨d38Announcement, by simp [d38Store], rfl⟩,
    d38_acceptAll_update_changes, d38_update_key_not_announced⟩

/-- The unconditional universal form is false in the wave-A model. -/
theorem waveD_d38_unconditional_attribution_false :
    ¬ (∀ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
        acceptChannelUpdate verify s u ≠ s → announcedKeyAdmitted s u) := by
  intro hall
  rcases waveD_d38_unannounced_key_counterexample with
    ⟨verify, s, u, _hann, haccept, hnot⟩
  exact hnot (hall verify s u haccept)

/-! ## The gate is not vacuous -/

/-- The same update with an announced signing key. -/
private def d38AdmittedUpdate : ChannelUpdate :=
  { d38Update with signingKey := d38KeyA }

/-- **Positive witness.**  An update whose signing key *is* announced passes
the admission gate and changes the store, so the conditional theorem is not
vacuous. -/
theorem waveD_d38_announced_key_admission_accepts :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      u.signatureValid verify ∧ announcedKeyAdmitted s u ∧
      acceptChannelUpdateAnnounced verify s u ≠ s := by
  have hsig : d38AdmittedUpdate.signatureValid d38AcceptAll := by
    simp [ChannelUpdate.signatureValid, signatureValid, d38AcceptAll]
  have hkey : announcedKeyAdmitted d38Store d38AdmittedUpdate :=
    ⟨d38Announcement, by simp [d38Store], rfl, Or.inl rfl⟩
  refine ⟨d38AcceptAll, d38Store, d38AdmittedUpdate, hsig, hkey, ?_⟩
  rw [waveD_d38_acceptChannelUpdateAnnounced_apply
    d38AcceptAll d38Store d38AdmittedUpdate hsig hkey]
  intro h
  have hu := congrArg GossipState.updates h
  simp [GossipState.applyUpdate, GossipState.latestUpdateTimestamp,
    latestTimestamp, d38Store, d38AdmittedUpdate, d38Update] at hu

/-- The accepted update of the positive witness is attributed to an announced
key, as the conditional theorem predicts. -/
theorem waveD_d38_announced_key_admission_attributed :
    ∃ (verify : SigVerifier) (s : GossipState) (u : ChannelUpdate),
      acceptChannelUpdateAnnounced verify s u ≠ s ∧
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        (a.nodeKey1 = u.signingKey ∨ a.nodeKey2 = u.signingKey) := by
  rcases waveD_d38_announced_key_admission_accepts with
    ⟨verify, s, u, _hsig, _hkey, hchange⟩
  exact ⟨verify, s, u, hchange,
    waveD_d38_accepted_update_signing_key_announced verify s u hchange⟩

end LnLean.Proofs.WaveD.D38
