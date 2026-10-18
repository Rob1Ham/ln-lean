import LnLean.Routing.Graph

/-!
# LnLean.Routing.Gossip

The BOLT 7 gossip messages and the monotone gossip state.

English claim of this module:

* `ChannelAnnellation` (BOLT 7 `channel_announcement`; the mission brief's
  spelling is kept as the primary name, with `ChannelAnnouncement` as an
  alias), `ChannelUpdate`, and `NodeAnnouncement` are the three gossip
  messages, each carrying a 64-byte signature over a digest.
* `ChannelUpdate.wellFormed` records the BOLT 7 sanity conditions needed by
  the model: a non-zero timestamp, a positive `cltv_expiry_delta`, and a
  minimum HTLC amount not exceeding the maximum.
* `GossipState.applyUpdate` accepts an update only when its `timestamp` is
  strictly greater than the newest timestamp already held (BOLT 7: "the
  timestamp ... MUST be greater than the timestamp of the previous
  `channel_update`").  Consequently the latest timestamp is monotone
  non-decreasing under `applyUpdate` and under `applyGossip`, and a stale
  update is a no-op.
* Signature predicates are *interfaces*: they take an abstract verifier and
  return a `Prop`.  No theorem here claims that a signature cannot be
  forged; that is assumption C3/C4/C8 in `docs/ASSUMPTIONS.md`.

BOLT sections:

* BOLT 7, "The `channel_announcement` Message" (four signatures: two
  `node_signature`s and two `bitcoin_signature`s; `short_channel_id`,
  `node_id_1`, `node_id_2`, `bitcoin_key_1`, `bitcoin_key_2`).
* BOLT 7, "The `channel_update` Message" (`timestamp`, `message_flags`,
  `channel_flags`, `cltv_expiry_delta`, `htlc_minimum_msat`,
  `fee_base_msat`, `fee_proportional_millionths`, `htlc_maximum_msat`,
  signature).
* BOLT 7, "The `node_announcement` Message" (`timestamp`, `node_id`,
  `rgb_color`, `alias`, `addresses`, signature).
* BOLT 7, "Pseudo-Descriptions" / "Updating the gossip store" (ignore an
  update whose timestamp is not greater than the stored one).

`rust-lightning` anchors (pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
line numbers are anchored to the symbol, see `agents/reports/A6.md` for the
pin-verification caveat):

* `lightning/src/routing/gossip.rs:600` — `pub struct ChannelUpdate`, the
  per-direction update fields and its `timestamp`.
* `lightning/src/routing/gossip.rs:1596` — `NetworkGraph::update_channel`,
  the timestamp comparison before replacing a `ChannelInfo` direction.
* `lightning/src/routing/gossip.rs:2050` — `NetworkGraph::handle_channel_update`
  (message-level entry point; signature check precedes insertion).
* `lightning/src/routing/gossip.rs:100` — `pub struct NodeInfo`, the
  `node_announcement` record.

What is **not** modelled:

* Wire encoding and the exact signed byte ranges (BOLT 7 signatures are
  double-SHA256 over the message with signature fields zeroed).  The digest
  is an opaque `ByteArray` field.
* Chain-hash filtering, UTXO verification of the funding outpoint, and the
  rule that `channel_announcement` must confirm on-chain.
* Address parsing (`node_announcement.addresses` is a `List ByteArray`).
* Gossip rate limits, `gossip_queries`, and peer-to-peer dissemination.
* Cryptographic unforgeability.  `SigVerifier` is an abstract function and
  `signatureValid` is its `= true` predicate, nothing more.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Signatures and verifiers -/

/-- A 64-byte BOLT 7 gossip signature.  BOLT 7 uses a compact (r,s) ECDSA
signature; the model keeps only the byte length and treats verification as
an abstract interface. -/
structure GossipSignature where
  bytes : ByteArray
deriving Repr, BEq

namespace GossipSignature

/-- BOLT 7 `signature` fields are 64 bytes. -/
def Valid (s : GossipSignature) : Prop := s.bytes.size = 64

end GossipSignature

/-- Abstract signature verifier: `verify key digest sig = true` means the
model accepts `sig` as a signature by `key` over `digest`.

The function is a parameter, never an axiom.  A theorem that needs
unforgeability must take the corresponding assumption (C3/C4 in
`docs/ASSUMPTIONS.md`) as a hypothesis. -/
abbrev SigVerifier := PubKey → ByteArray → GossipSignature → Bool

/-- The `Prop` counterpart of a verifier result. -/
def signatureValid (verify : SigVerifier) (key : PubKey) (digest : ByteArray)
    (sig : GossipSignature) : Prop :=
  verify key digest sig = true

/-! ## Messages -/

/-- BOLT 7 `channel_announcement`.

The announcement binds a `short_channel_id` to two node ids and two Bitcoin
funding keys, and carries four signatures over the same digest.  The model
does not require the capacity to be positive; BOLT 7's "capacity is the
funding output value" sanity check is an obligation, not a field invariant. -/
structure ChannelAnnellation where
  shortChannelId : ShortChannelId
  node1 : NodeId
  node2 : NodeId
  nodeKey1 : PubKey
  nodeKey2 : PubKey
  bitcoinKey1 : PubKey
  bitcoinKey2 : PubKey
  capacitySat : Nat
  digest : ByteArray
  nodeSignature1 : GossipSignature
  nodeSignature2 : GossipSignature
  bitcoinSignature1 : GossipSignature
  bitcoinSignature2 : GossipSignature
deriving Repr, BEq

/-- The BOLT 7 spelling of the same message, kept so downstream modules can
use the unmangled name. -/
abbrev ChannelAnnouncement := ChannelAnnellation

namespace ChannelAnnellation

/-- All four BOLT 7 signatures verify under the announced keys. -/
def signaturesValid (verify : SigVerifier) (a : ChannelAnnellation) : Prop :=
  signatureValid verify a.nodeKey1 a.digest a.nodeSignature1 ∧
  signatureValid verify a.nodeKey2 a.digest a.nodeSignature2 ∧
  signatureValid verify a.bitcoinKey1 a.digest a.bitcoinSignature1 ∧
  signatureValid verify a.bitcoinKey2 a.digest a.bitcoinSignature2

/-- A successful four-way check entails each individual signature. -/
theorem node1_signature_valid {verify : SigVerifier} {a : ChannelAnnellation}
    (h : a.signaturesValid verify) :
    signatureValid verify a.nodeKey1 a.digest a.nodeSignature1 :=
  h.1

theorem node2_signature_valid {verify : SigVerifier} {a : ChannelAnnellation}
    (h : a.signaturesValid verify) :
    signatureValid verify a.nodeKey2 a.digest a.nodeSignature2 :=
  h.2.1

end ChannelAnnellation

/-- BOLT 7 `channel_update`, i.e. one direction of a channel.

`messageFlags` bit 0 is `option_channel_htlc_max`; `channelFlags` bit 0 is
`direction` and bit 1 is `disable`.  The model stores the raw integers and
does not decode individual bits. -/
structure ChannelUpdate where
  shortChannelId : ShortChannelId
  timestamp : Timestamp
  messageFlags : Nat
  channelFlags : Nat
  cltvDelta : Nat
  htlcMinimumMsat : Msat
  feeBaseMsat : Msat
  feeProportionalMillionths : Nat
  htlcMaximumMsat : Msat
  signingKey : PubKey
  digest : ByteArray
  signature : GossipSignature
deriving Repr, BEq

namespace ChannelUpdate

/-- The single BOLT 7 signature of a `channel_update`. -/
def signatureValid (verify : SigVerifier) (u : ChannelUpdate) : Prop :=
  LnLean.Routing.signatureValid verify u.signingKey u.digest u.signature

/-- BOLT 7 sanity conditions used by this model.  The spec's additional
"must be at least the chain's minimum" rule is a policy parameter and is not
included. -/
def wellFormed (u : ChannelUpdate) : Prop :=
  u.timestamp ≠ 0 ∧ 0 < u.cltvDelta ∧
    u.htlcMinimumMsat.val ≤ u.htlcMaximumMsat.val

theorem wellFormed_timestamp_ne_zero {u : ChannelUpdate}
    (h : u.wellFormed) : u.timestamp ≠ 0 := h.1

theorem wellFormed_cltvDelta_pos {u : ChannelUpdate}
    (h : u.wellFormed) : 0 < u.cltvDelta := h.2.1

theorem wellFormed_htlc_min_le_max {u : ChannelUpdate}
    (h : u.wellFormed) : u.htlcMinimumMsat.val ≤ u.htlcMaximumMsat.val := h.2.2

/-- BOLT 7 replacement rule: `u` supersedes `old` iff its timestamp is
strictly greater.  Equal timestamps do not replace (tie-breaking would need
a total order on signatures, which BOLT 7 deliberately avoids). -/
def isNewerThan (u old : ChannelUpdate) : Prop := old.timestamp < u.timestamp

end ChannelUpdate

/-- BOLT 7 `node_announcement`. -/
structure NodeAnnouncement where
  nodeId : PubKey
  timestamp : Timestamp
  rgbColor : ByteArray
  alias : ByteArray
  addresses : List ByteArray
  digest : ByteArray
  signature : GossipSignature
deriving Repr, BEq

namespace NodeAnnouncement

def signatureValid (verify : SigVerifier) (n : NodeAnnouncement) : Prop :=
  LnLean.Routing.signatureValid verify n.nodeId n.digest n.signature

end NodeAnnouncement

/-- The three BOLT 7 gossip messages. -/
inductive GossipMessage where
  | channelAnnouncement (a : ChannelAnnellation)
  | channelUpdate (u : ChannelUpdate)
  | nodeAnnouncement (n : NodeAnnouncement)
deriving Repr, BEq

/-! ## Gossip state and timestamp monotonicity -/

/-- The newest `channel_update` timestamp in a list.  Folding with `max`
makes monotonicity a one-line induction. -/
def latestTimestamp (updates : List ChannelUpdate) : Timestamp :=
  updates.foldl (fun acc u => max acc u.timestamp) 0

theorem latestTimestamp_nil : latestTimestamp [] = 0 := rfl

/-- The fold is monotone in its accumulator. -/
theorem foldl_max_mono (l : List ChannelUpdate) {a b : Nat} (h : a ≤ b) :
    l.foldl (fun acc u => max acc u.timestamp) a ≤
      l.foldl (fun acc u => max acc u.timestamp) b := by
  induction l generalizing a b with
  | nil => exact h
  | cons u us ih =>
    simp only [List.foldl_cons]
    exact ih ((Nat.max_le).mpr ⟨Nat.le_trans h (Nat.le_max_left b u.timestamp),
      Nat.le_max_right b u.timestamp⟩)

/-- The fold never decreases its accumulator. -/
theorem foldl_max_ge (l : List ChannelUpdate) (a : Nat) :
    a ≤ l.foldl (fun acc u => max acc u.timestamp) a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl a
  | cons u us ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left a u.timestamp)
      (ih (max a u.timestamp))

/-- Every stored update's timestamp is at most the stored latest timestamp. -/
theorem mem_timestamp_le_latest {u : ChannelUpdate} {l : List ChannelUpdate}
    (h : u ∈ l) : u.timestamp ≤ latestTimestamp l := by
  induction l with
  | nil => simp at h
  | cons v vs ih =>
    simp only [latestTimestamp, List.foldl_cons]
    rcases List.mem_cons.mp h with hEq | hmem
    · cases hEq
      exact Nat.le_trans (Nat.le_max_right 0 u.timestamp)
        (foldl_max_ge vs (max 0 u.timestamp))
    · exact Nat.le_trans (ih hmem)
        (foldl_max_mono vs (Nat.le_max_left 0 v.timestamp))

/-- The modelled gossip store.  It keeps the raw history rather than
replacing per-direction entries; `latestUpdateTimestamp` is the replacement
clock.  A production store keys updates by `(short_channel_id, direction)`,
which is deliberately not modelled here. -/
structure GossipState where
  announcements : List ChannelAnnellation
  updates : List ChannelUpdate
  nodeAnnouncements : List NodeAnnouncement
deriving Repr, BEq

namespace GossipState

/-- Newest timestamp among all stored channel updates. -/
def latestUpdateTimestamp (s : GossipState) : Timestamp :=
  latestTimestamp s.updates

/-- Insert an update only if it is strictly newer than everything stored.
This is the BOLT 7 "ignore stale `channel_update`" rule in its weakest
sound form: the store is append-only, and the clock never goes backwards. -/
def applyUpdate (s : GossipState) (u : ChannelUpdate) : GossipState :=
  if s.latestUpdateTimestamp < u.timestamp then
    { s with updates := u :: s.updates }
  else s

/-- `applyUpdate` never lowers the gossip clock. -/
theorem latestUpdateTimestamp_applyUpdate_ge (s : GossipState)
    (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤ (s.applyUpdate u).latestUpdateTimestamp := by
  unfold applyUpdate
  split
  · unfold latestUpdateTimestamp
    simp only [latestTimestamp, List.foldl_cons]
    exact foldl_max_mono s.updates (Nat.zero_le (max 0 u.timestamp))
  · exact Nat.le_refl s.latestUpdateTimestamp

/-- A stale update leaves the store unchanged. -/
theorem applyUpdate_stale (s : GossipState) (u : ChannelUpdate)
    (h : u.timestamp ≤ s.latestUpdateTimestamp) : s.applyUpdate u = s := by
  unfold applyUpdate
  rw [ite_eq_right (Nat.not_lt_of_le h)]

/-- A strictly newer update is stored at the head and becomes the clock. -/
theorem applyUpdate_new (s : GossipState) (u : ChannelUpdate)
    (h : s.latestUpdateTimestamp < u.timestamp) :
    (s.applyUpdate u).updates = u :: s.updates := by
  unfold applyUpdate
  rw [ite_eq_left h]

/-- All updates present before an insertion remain present. -/
theorem applyUpdate_mem_old (s : GossipState) (u v : ChannelUpdate)
    (h : v ∈ s.updates) : v ∈ (s.applyUpdate u).updates := by
  unfold applyUpdate
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

end GossipState

/-- Apply one gossip message to the store.  Announcements are appended to
their respective lists; only `channel_update` affects the timestamp clock. -/
def applyGossip (s : GossipState) : GossipMessage → GossipState
  | .channelAnnouncement a => { s with announcements := a :: s.announcements }
  | .channelUpdate u => s.applyUpdate u
  | .nodeAnnouncement n => { s with nodeAnnouncements := n :: s.nodeAnnouncements }

/-- **Gossip timestamp monotonicity.**  Applying any gossip message never
lowers the newest `channel_update` timestamp. -/
theorem applyGossip_timestamp_monotone (s : GossipState) (m : GossipMessage) :
    s.latestUpdateTimestamp ≤ (applyGossip s m).latestUpdateTimestamp := by
  cases m with
  | channelAnnouncement a => exact Nat.le_refl s.latestUpdateTimestamp
  | channelUpdate u => exact GossipState.latestUpdateTimestamp_applyUpdate_ge s u
  | nodeAnnouncement n => exact Nat.le_refl s.latestUpdateTimestamp

/-- A stale `channel_update` delivered as a message is a no-op on the whole
store. -/
theorem applyGossip_stale_update (s : GossipState) (u : ChannelUpdate)
    (h : u.timestamp ≤ s.latestUpdateTimestamp) :
    applyGossip s (.channelUpdate u) = s :=
  GossipState.applyUpdate_stale s u h

/-! ## Replacement rule (catalog target `LN-RT-002`) -/

namespace Gossip

/-- **Gossip timestamp monotonicity and replacement rule**
(catalog target `LnLean.Routing.Gossip.update_monotone`, `LN-RT-002`).

Both halves of the BOLT 7 `channel_update` replacement claim are recorded:

* the newest stored timestamp never decreases under
  `GossipState.applyUpdate`;
* if an update actually changes the store, then the update's timestamp was
  strictly greater than the old clock.  Thus an older (or equally old) update
  can never replace the stored one; a replacement requires a strictly greater
  timestamp.

The second half is the contrapositive of `GossipState.applyUpdate_stale`; no
positivity or `wellFormed` hypothesis is needed, because the replacement
guard itself compares the timestamps. -/
theorem update_monotone (s : GossipState) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤ (s.applyUpdate u).latestUpdateTimestamp ∧
      (s.applyUpdate u ≠ s → s.latestUpdateTimestamp < u.timestamp) := by
  refine ⟨GossipState.latestUpdateTimestamp_applyUpdate_ge s u, ?_⟩
  intro hchange
  by_cases hle : u.timestamp ≤ s.latestUpdateTimestamp
  · exact absurd (GossipState.applyUpdate_stale s u hle) hchange
  · exact Nat.lt_of_not_le hle

end Gossip

/-! ## Key attribution for `channel_update` admission (additive, `RT-01`)

The store above accepts a `channel_update` on its timestamp alone, and
`LnLean.Proofs.Routing.GossipProps.acceptChannelUpdate` adds only the
abstract signature check.  BOLT 7 additionally takes the `node_id` used to
verify a `channel_update` from the matching `channel_announcement`
(`refs/bolts/07-routing-gossip.md:544`).  The definitions below make that
relation explicit:

* `ChannelAnnellation.attributesKey a key` says that `key` is one of the two
  BOLT 7 `node_id` keys carried by `a`;
* `GossipState.updateKeyAnnounced s u` says that some stored announcement for
  `u.shortChannelId` attributes `u.signingKey`;
* `GossipState.applyUpdateAttributed` is an *additional* store step that
  requires both the signature predicate and `updateKeyAnnounced`.

Nothing in this section changes `GossipState.applyUpdate`, `applyGossip`, or
any existing statement: the attributed step is a separate function, so the
raw-store behaviour and all wave-A theorems remain intact.  The relation
checks key *equality with an announcement field*; it does not claim that the
announcement itself verified (that is the separate signature gate) nor that
the key is owned by the graph node (see `KeyAttribution` in
`LnLean.Proofs.Routing.GossipTargets`). -/

namespace ChannelAnnellation

/-- **Key attribution to an announcement.**  `a.attributesKey key` holds when
`key` is one of the two BOLT 7 `node_id` keys that `a` announces for its
channel.  This is the key set from which a valid `channel_update` signature
key must be drawn. -/
def attributesKey (a : ChannelAnnellation) (key : PubKey) : Prop :=
  a.nodeKey1 = key ∨ a.nodeKey2 = key

/-- **Exact unfolding** of `attributesKey`: a disjunction of the two announced
node keys, with no hidden conjunct. -/
theorem attributesKey_iff (a : ChannelAnnellation) (key : PubKey) :
    a.attributesKey key ↔ a.nodeKey1 = key ∨ a.nodeKey2 = key :=
  Iff.rfl

/-- The first announced node key is attributed. -/
theorem attributesKey_node1 (a : ChannelAnnellation) :
    a.attributesKey a.nodeKey1 :=
  Or.inl rfl

/-- The second announced node key is attributed. -/
theorem attributesKey_node2 (a : ChannelAnnellation) :
    a.attributesKey a.nodeKey2 :=
  Or.inr rfl

end ChannelAnnellation

namespace GossipState

/-- **`updateKeyAnnounced s u`**: some stored `channel_announcement` for the
same `short_channel_id` names `u.signingKey` as one of its two BOLT 7 node
keys.

This is the missing admission predicate from `RT-01` (`LN-GOSSIP-001`).  It
is a proposition over the current store and deliberately does not include
signature validity: the signature gate is separate, and in reachable admitted
states every stored announcement is valid by construction. -/
def updateKeyAnnounced (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    a.attributesKey u.signingKey

/-- **Exact unfolding** of `updateKeyAnnounced`. -/
theorem updateKeyAnnounced_iff (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnounced u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        a.attributesKey u.signingKey :=
  Iff.rfl

/-- Introduction form: a stored announcement for the same channel that
attributes the update's signing key witnesses `updateKeyAnnounced`. -/
theorem updateKeyAnnounced_of_mem {s : GossipState} {u : ChannelUpdate}
    {a : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hscid : a.shortChannelId = u.shortChannelId)
    (hkey : a.attributesKey u.signingKey) :
    s.updateKeyAnnounced u :=
  ⟨a, ha, hscid, hkey⟩

/-- Attribution is monotone in the announcement list: growing the store with
further announcements cannot un-announce a key. -/
theorem updateKeyAnnounced_mono {s t : GossipState} {u : ChannelUpdate}
    (hsub : ∀ a ∈ s.announcements, a ∈ t.announcements)
    (h : s.updateKeyAnnounced u) : t.updateKeyAnnounced u := by
  rcases h with ⟨a, ha, hscid, hkey⟩
  exact ⟨a, hsub a ha, hscid, hkey⟩

/-- Accepting or ignoring an update never changes the announcement list. -/
theorem applyUpdate_announcements (s : GossipState) (u : ChannelUpdate) :
    (s.applyUpdate u).announcements = s.announcements := by
  unfold applyUpdate
  split <;> rfl

/-- An announced key stays announced after the wave-A update step. -/
theorem updateKeyAnnounced_applyUpdate (s : GossipState) (u : ChannelUpdate)
    (h : s.updateKeyAnnounced u) :
    (s.applyUpdate u).updateKeyAnnounced u := by
  refine updateKeyAnnounced_mono ?_ h
  intro a ha
  rw [applyUpdate_announcements]
  exact ha

open Classical

/-- **Attributed `channel_update` store step.**  It differs from wave-A
`GossipState.applyUpdate` by the extra guard: the update's abstract signature
must verify *and* its signing key must be announced for the same channel.  It
is an additional function; `applyUpdate` itself is unchanged. -/
noncomputable def applyUpdateAttributed (s : GossipState) (verify : SigVerifier)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify ∧ s.updateKeyAnnounced u then s.applyUpdate u else s

/-- When both admission conditions hold, the attributed step is exactly the
wave-A update step: attribution is the only extra gate. -/
theorem applyUpdateAttributed_eq_applyUpdate_of_admitted (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hsig : u.signatureValid verify) (hk : s.updateKeyAnnounced u) :
    s.applyUpdateAttributed verify u = s.applyUpdate u := by
  unfold applyUpdateAttributed
  rw [ite_eq_left ⟨hsig, hk⟩]

/-- An update whose key was not announced is rejected outright, regardless of
its signature. -/
theorem applyUpdateAttributed_eq_self_of_unannounced (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hk : ¬ s.updateKeyAnnounced u) :
    s.applyUpdateAttributed verify u = s := by
  unfold applyUpdateAttributed
  rw [ite_eq_right]
  rintro ⟨_, hk'⟩
  exact hk hk'

/-- **Soundness of attributed admission.**  Any change made by the attributed
step requires both the signature predicate and an announced signing key. -/
theorem applyUpdateAttributed_change_requires (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateAttributed verify u ≠ s) :
    u.signatureValid verify ∧ s.updateKeyAnnounced u := by
  apply Classical.byContradiction
  intro hcon
  apply h
  unfold applyUpdateAttributed
  rw [ite_eq_right]
  rintro ⟨hsig, hk⟩
  exact hcon ⟨hsig, hk⟩

/-- Any change made by the attributed step also requires a strictly newer
timestamp, because the underlying replacement rule is unchanged. -/
theorem applyUpdateAttributed_change_requires_newer (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateAttributed verify u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  by_cases hnew : s.latestUpdateTimestamp < u.timestamp
  · exact hnew
  · have hle : u.timestamp ≤ s.latestUpdateTimestamp := Nat.le_of_not_lt hnew
    have heq : s.applyUpdateAttributed verify u = s := by
      unfold applyUpdateAttributed
      split
      · exact applyUpdate_stale s u hle
      · rfl
    exact absurd heq h

/-- The attributed step never changes the announcement list. -/
theorem applyUpdateAttributed_announcements (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    (s.applyUpdateAttributed verify u).announcements = s.announcements := by
  unfold applyUpdateAttributed
  split
  · exact applyUpdate_announcements s u
  · rfl

/-- An announced key stays announced after the attributed step. -/
theorem updateKeyAnnounced_applyUpdateAttributed (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) (h : s.updateKeyAnnounced u) :
    (s.applyUpdateAttributed verify u).updateKeyAnnounced u := by
  refine updateKeyAnnounced_mono ?_ h
  intro a ha
  rw [applyUpdateAttributed_announcements]
  exact ha

/-- The attributed step never lowers the gossip clock. -/
theorem latestUpdateTimestamp_applyUpdateAttributed_ge (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤
      (s.applyUpdateAttributed verify u).latestUpdateTimestamp := by
  unfold applyUpdateAttributed
  split
  · exact latestUpdateTimestamp_applyUpdate_ge s u
  · exact Nat.le_refl s.latestUpdateTimestamp

end GossipState

/-! ## Direction-keyed update signing, node-key consistency, and announcement
deduplication (additive, `RT-01`, wave 5)

The wave-4 relation `GossipState.updateKeyAnnounced` accepts either announced
node key for a `channel_update`, because it does not decode the BOLT 7
`channel_flags` direction bit.  BOLT 7 is stricter: the direction bit selects
which endpoint sends the update and therefore which `node_id` signs it.

This section adds, without changing any existing definition or theorem:

* `ChannelUpdate.direction`, the decoded `channel_flags` bit 0
  (`false` = direction 0, node 1 to node 2; `true` = direction 1, node 2 to
  node 1);
* `ChannelAnnellation.attributesKeyForDirection`, the direction-selected
  announced key (direction 0 uses `nodeKey1`, direction 1 uses `nodeKey2`);
* `GossipState.updateKeyAnnouncedDirectional`, the direction-keyed
  attribution relation, and the additional store step
  `GossipState.applyUpdateDirected`;
* `GossipState.NodeKeyConsistent`, the explicit `NodeId → PubKey`
  consistency invariant (the missing map from wave A);
* `CanonicalAnnouncements`, `dedupAnnouncements`, and
  `GossipState.canonicalView`, a canonical announcement view that removes
  same-`short_channel_id` duplicates.

All of these are definitions and lemmas.  `applyGossip`, `applyUpdate`, and
the wave-4 `applyUpdateAttributed` keep their exact signatures and behaviour.
The raw store is still append-only and still neither signature-filtered nor
deduplicated. -/

namespace ChannelUpdate

/-- BOLT 7 `channel_flags` bit 0, decoded: `false` is direction 0
(`node_1` to `node_2`) and `true` is direction 1 (`node_2` to `node_1`). -/
def direction (u : ChannelUpdate) : Bool :=
  u.channelFlags % 2 == 1

/-- The decoded direction is exactly the low bit of `channel_flags`. -/
theorem direction_eq_true_iff (u : ChannelUpdate) :
    u.direction = true ↔ u.channelFlags % 2 = 1 := by
  unfold direction
  by_cases h : u.channelFlags % 2 = 1
  · simp [h]
  · have h0 : u.channelFlags % 2 = 0 := by omega
    simp [h0]

/-- The complement form: `false` is direction 0. -/
theorem direction_eq_false_iff (u : ChannelUpdate) :
    u.direction = false ↔ u.channelFlags % 2 = 0 := by
  unfold direction
  by_cases h : u.channelFlags % 2 = 1
  · simp [h]
  · have h0 : u.channelFlags % 2 = 0 := by omega
    simp [h0]

/-- `channel_flags = 0` is direction 0. -/
theorem direction_of_channelFlags_zero {u : ChannelUpdate}
    (h : u.channelFlags = 0) : u.direction = false := by
  rw [direction_eq_false_iff, h]

/-- `channel_flags = 1` is direction 1. -/
theorem direction_of_channelFlags_one {u : ChannelUpdate}
    (h : u.channelFlags = 1) : u.direction = true := by
  rw [direction_eq_true_iff, h]

end ChannelUpdate

namespace ChannelAnnellation

/-- **Direction-keyed announced key.**  Direction 0 updates must be signed by
`nodeKey1`; direction 1 updates must be signed by `nodeKey2`.  This is the
BOLT 7 direction-to-node-key rule, stated as a predicate over the
announcement and the decoded direction. -/
def attributesKeyForDirection (a : ChannelAnnellation) (direction : Bool)
    (key : PubKey) : Prop :=
  if direction then a.nodeKey2 = key else a.nodeKey1 = key

/-- **Exact unfolding** of the direction-keyed relation. -/
theorem attributesKeyForDirection_iff (a : ChannelAnnellation) (direction : Bool)
    (key : PubKey) :
    a.attributesKeyForDirection direction key ↔
      (direction = false ∧ a.nodeKey1 = key) ∨
        (direction = true ∧ a.nodeKey2 = key) := by
  cases direction <;> simp [attributesKeyForDirection]

/-- Direction 0 attributes the first announced node key. -/
theorem attributesKeyForDirection_node1 (a : ChannelAnnellation) :
    a.attributesKeyForDirection false a.nodeKey1 := by
  simp [attributesKeyForDirection]

/-- Direction 1 attributes the second announced node key. -/
theorem attributesKeyForDirection_node2 (a : ChannelAnnellation) :
    a.attributesKeyForDirection true a.nodeKey2 := by
  simp [attributesKeyForDirection]

/-- **Direction keying refines the wave-4 key set.**  A direction-correct key
is always one of the two announced node keys, so the directional gate is
stronger than `attributesKey`.  The converse fails
(`directional_attribution_of_general_fails` in
`LnLean.Proofs.Routing.GossipKeyConsistencyTargets`). -/
theorem attributesKeyForDirection_implies_attributesKey (a : ChannelAnnellation)
    (direction : Bool) (key : PubKey)
    (h : a.attributesKeyForDirection direction key) : a.attributesKey key := by
  by_cases hd : direction
  · rw [attributesKeyForDirection, ite_eq_left hd] at h
    exact Or.inr h
  · rw [attributesKeyForDirection, ite_eq_right hd] at h
    exact Or.inl h

end ChannelAnnellation

/-! ### Direction-keyed attribution in the store -/

namespace GossipState

open Classical

/-- **Direction-keyed update-key attribution.**  Some stored announcement for
the update's channel names the direction-appropriate endpoint key as the
update's signing key.  This is the BOLT 7 key check with the direction bit
decoded, and it is strictly stronger than the wave-4
`updateKeyAnnounced`. -/
def updateKeyAnnouncedDirectional (s : GossipState) (u : ChannelUpdate) : Prop :=
  ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
    a.attributesKeyForDirection u.direction u.signingKey

/-- **Exact unfolding** of the direction-keyed relation. -/
theorem updateKeyAnnouncedDirectional_iff (s : GossipState) (u : ChannelUpdate) :
    s.updateKeyAnnouncedDirectional u ↔
      ∃ a ∈ s.announcements, a.shortChannelId = u.shortChannelId ∧
        a.attributesKeyForDirection u.direction u.signingKey :=
  Iff.rfl

/-- Introduction form: a stored same-channel announcement that attributes the
direction-selected key witnesses direction-keyed attribution. -/
theorem updateKeyAnnouncedDirectional_of_mem {s : GossipState}
    {u : ChannelUpdate} {a : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hscid : a.shortChannelId = u.shortChannelId)
    (hkey : a.attributesKeyForDirection u.direction u.signingKey) :
    s.updateKeyAnnouncedDirectional u :=
  ⟨a, ha, hscid, hkey⟩

/-- Direction-keyed attribution is monotone in the announcement list. -/
theorem updateKeyAnnouncedDirectional_mono {s t : GossipState}
    {u : ChannelUpdate}
    (hsub : ∀ a ∈ s.announcements, a ∈ t.announcements)
    (h : s.updateKeyAnnouncedDirectional u) :
    t.updateKeyAnnouncedDirectional u := by
  rcases h with ⟨a, ha, hscid, hkey⟩
  exact ⟨a, hsub a ha, hscid, hkey⟩

/-- **The directional gate implies the wave-4 gate.**  Every direction-correct
key is one of the two announced keys, but not conversely. -/
theorem updateKeyAnnouncedDirectional_implies_updateKeyAnnounced
    (s : GossipState) (u : ChannelUpdate)
    (h : s.updateKeyAnnouncedDirectional u) : s.updateKeyAnnounced u := by
  rcases h with ⟨a, ha, hscid, hkey⟩
  exact ⟨a, ha, hscid,
    a.attributesKeyForDirection_implies_attributesKey u.direction u.signingKey hkey⟩

/-- An announced direction-correct key stays announced after wave-A
`applyUpdate`. -/
theorem updateKeyAnnouncedDirectional_applyUpdate (s : GossipState)
    (u : ChannelUpdate) (h : s.updateKeyAnnouncedDirectional u) :
    (s.applyUpdate u).updateKeyAnnouncedDirectional u := by
  refine updateKeyAnnouncedDirectional_mono ?_ h
  intro a ha
  rw [applyUpdate_announcements]
  exact ha

/-- **Directed attributed `channel_update` store step.**  It differs from the
wave-4 `applyUpdateAttributed` only by using the direction-selected key.  The
underlying timestamp replacement is exactly `applyUpdate`. -/
noncomputable def applyUpdateDirected (s : GossipState) (verify : SigVerifier)
    (u : ChannelUpdate) : GossipState :=
  if u.signatureValid verify ∧ s.updateKeyAnnouncedDirectional u then
    s.applyUpdate u
  else s

/-- When both directed admission conditions hold, the directed step is the
wave-A update step. -/
theorem applyUpdateDirected_eq_applyUpdate_of_admitted (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hsig : u.signatureValid verify)
    (hk : s.updateKeyAnnouncedDirectional u) :
    s.applyUpdateDirected verify u = s.applyUpdate u := by
  unfold applyUpdateDirected
  rw [ite_eq_left ⟨hsig, hk⟩]

/-- A directionally unannounced update is rejected outright. -/
theorem applyUpdateDirected_eq_self_of_unannounced (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (hk : ¬ s.updateKeyAnnouncedDirectional u) :
    s.applyUpdateDirected verify u = s := by
  unfold applyUpdateDirected
  rw [ite_eq_right]
  rintro ⟨_, hk'⟩
  exact hk hk'

/-- **Soundness of directed admission.**  Any change requires the signature
predicate and direction-keyed attribution. -/
theorem applyUpdateDirected_change_requires (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateDirected verify u ≠ s) :
    u.signatureValid verify ∧ s.updateKeyAnnouncedDirectional u := by
  apply Classical.byContradiction
  intro hcon
  apply h
  unfold applyUpdateDirected
  rw [ite_eq_right]
  rintro ⟨hsig, hk⟩
  exact hcon ⟨hsig, hk⟩

/-- The directed step still requires a strictly newer timestamp. -/
theorem applyUpdateDirected_change_requires_newer (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.applyUpdateDirected verify u ≠ s) :
    s.latestUpdateTimestamp < u.timestamp := by
  by_cases hnew : s.latestUpdateTimestamp < u.timestamp
  · exact hnew
  · have hle : u.timestamp ≤ s.latestUpdateTimestamp := Nat.le_of_not_lt hnew
    have heq : s.applyUpdateDirected verify u = s := by
      unfold applyUpdateDirected
      split
      · exact applyUpdate_stale s u hle
      · rfl
    exact absurd heq h

/-- The directed step never changes the announcement list. -/
theorem applyUpdateDirected_announcements (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    (s.applyUpdateDirected verify u).announcements = s.announcements := by
  unfold applyUpdateDirected
  split
  · exact applyUpdate_announcements s u
  · rfl

/-- A direction-correct announced key stays announced after the directed
step. -/
theorem updateKeyAnnouncedDirectional_applyUpdateDirected
    (s : GossipState) (verify : SigVerifier) (u : ChannelUpdate)
    (h : s.updateKeyAnnouncedDirectional u) :
    (s.applyUpdateDirected verify u).updateKeyAnnouncedDirectional u := by
  refine updateKeyAnnouncedDirectional_mono ?_ h
  intro a ha
  rw [applyUpdateDirected_announcements]
  exact ha

/-- The directed step never lowers the gossip clock. -/
theorem latestUpdateTimestamp_applyUpdateDirected_ge (s : GossipState)
    (verify : SigVerifier) (u : ChannelUpdate) :
    s.latestUpdateTimestamp ≤
      (s.applyUpdateDirected verify u).latestUpdateTimestamp := by
  unfold applyUpdateDirected
  split
  · exact latestUpdateTimestamp_applyUpdate_ge s u
  · exact Nat.le_refl s.latestUpdateTimestamp

/-! ### `NodeId → PubKey` consistency -/

/-- **Node-key consistency invariant.**  An explicit graph-node to BOLT 7 key
map agrees with every stored announcement: `nodeKeyOf a.node1 = a.nodeKey1`
and `nodeKeyOf a.node2 = a.nodeKey2`.  Wave A has no such map; this predicate
is the invariant a production admission path must maintain. -/
def NodeKeyConsistent (nodeKeyOf : NodeId → PubKey) (s : GossipState) : Prop :=
  ∀ a ∈ s.announcements, nodeKeyOf a.node1 = a.nodeKey1 ∧
    nodeKeyOf a.node2 = a.nodeKey2

/-- The empty store is consistent for every map. -/
theorem nodeKeyConsistent_empty (nodeKeyOf : NodeId → PubKey) :
    NodeKeyConsistent nodeKeyOf ⟨[], [], []⟩ := by
  intro a ha
  simp at ha

/-- Node-key consistency is monotone in the announcement list. -/
theorem nodeKeyConsistent_mono {nodeKeyOf : NodeId → PubKey}
    {s t : GossipState}
    (hsub : ∀ a ∈ t.announcements, a ∈ s.announcements)
    (h : NodeKeyConsistent nodeKeyOf s) : NodeKeyConsistent nodeKeyOf t := by
  intro a ha
  exact h a (hsub a ha)

/-- Accepting an update preserves node-key consistency. -/
theorem nodeKeyConsistent_applyUpdate {nodeKeyOf : NodeId → PubKey}
    (s : GossipState) (u : ChannelUpdate)
    (h : NodeKeyConsistent nodeKeyOf s) :
    NodeKeyConsistent nodeKeyOf (s.applyUpdate u) := by
  refine nodeKeyConsistent_mono ?_ h
  intro a ha
  rw [applyUpdate_announcements] at ha
  exact ha

/-- **Consistency implies agreement across announcements.**  If two stored
announcements name the same graph node, the map forces the same BOLT 7 key.
This is the uniqueness content of the invariant. -/
theorem nodeKeyConsistent_node1_key_unique {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : NodeKeyConsistent nodeKeyOf s)
    {a b : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hb : b ∈ s.announcements) (hnode : a.node1 = b.node1) :
    a.nodeKey1 = b.nodeKey1 := by
  have ha' := (h a ha).1
  have hb' := (h b hb).1
  rw [hnode] at ha'
  exact ha'.symm.trans hb'

/-- The second-endpoint form of `nodeKeyConsistent_node1_key_unique`. -/
theorem nodeKeyConsistent_node2_key_unique {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : NodeKeyConsistent nodeKeyOf s)
    {a b : ChannelAnnellation} (ha : a ∈ s.announcements)
    (hb : b ∈ s.announcements) (hnode : a.node2 = b.node2) :
    a.nodeKey2 = b.nodeKey2 := by
  have ha' := (h a ha).2
  have hb' := (h b hb).2
  rw [hnode] at ha'
  exact ha'.symm.trans hb'

end GossipState

/-! ### Canonical announcement view and deduplication -/

/-- **Canonical announcements.**  No two stored announcements with the same
`short_channel_id` are distinct.  Under this invariant a channel has exactly
one announcement record, so endpoint keys and direction keys cannot be
ambiguous.  The raw store does not maintain it. -/
def CanonicalAnnouncements (l : List ChannelAnnellation) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, a.shortChannelId = b.shortChannelId → a = b

/-- Boolean test for the channel identity used by the deduplicator. -/
def sameScid (a b : ChannelAnnellation) : Bool :=
  decide (a.shortChannelId = b.shortChannelId)

/-- Exact unfolding of `sameScid`. -/
theorem sameScid_eq_true_iff (a b : ChannelAnnellation) :
    sameScid a b = true ↔ a.shortChannelId = b.shortChannelId := by
  simp [sameScid]

/-- The complement form of `sameScid`. -/
theorem sameScid_eq_false_iff (a b : ChannelAnnellation) :
    sameScid a b = false ↔ a.shortChannelId ≠ b.shortChannelId := by
  by_cases h : a.shortChannelId = b.shortChannelId
  · simp [sameScid, h]
  · simp [sameScid, h]

/-- Insert an announcement into a list only when the list has no announcement
for the same `short_channel_id`.  The existing (later in the input) record
wins, so the fold below keeps the last occurrence of each channel. -/
def insertCanonical (a : ChannelAnnellation)
    (l : List ChannelAnnellation) : List ChannelAnnellation :=
  if l.any (sameScid a) then l else a :: l

/-- Membership in `insertCanonical` is either the new announcement or an old
one. -/
theorem mem_insertCanonical_cases {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ insertCanonical a l) :
    b = a ∨ b ∈ l := by
  unfold insertCanonical at h
  split at h
  · exact Or.inr h
  · rcases List.mem_cons.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

/-- Insertion preserves all old members. -/
theorem mem_insertCanonical_of_mem {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ l) :
    b ∈ insertCanonical a l := by
  unfold insertCanonical
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- **Canonical deduplication.**  Keep the last stored announcement for each
`short_channel_id`.  This is a canonical *view*; the raw store is not changed. -/
def dedupAnnouncements (l : List ChannelAnnellation) : List ChannelAnnellation :=
  l.foldr insertCanonical []

/-- Unfolding of the deduplicator at a cons. -/
theorem dedupAnnouncements_cons (a : ChannelAnnellation)
    (l : List ChannelAnnellation) :
    dedupAnnouncements (a :: l) = insertCanonical a (dedupAnnouncements l) :=
  rfl

/-- Deduplication only removes announcements; it never invents one. -/
theorem mem_of_mem_dedupAnnouncements {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : a ∈ dedupAnnouncements l) : a ∈ l := by
  induction l with
  | nil => simp [dedupAnnouncements] at h
  | cons b bs ih =>
      rw [dedupAnnouncements_cons] at h
      rcases mem_insertCanonical_cases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- **The deduplicated view is canonical.**  No two distinct announcements
with the same `short_channel_id` survive. -/
theorem canonical_dedupAnnouncements (l : List ChannelAnnellation) :
    CanonicalAnnouncements (dedupAnnouncements l) := by
  induction l with
  | nil =>
      intro a ha
      simp [dedupAnnouncements] at ha
  | cons b bs ih =>
      rw [dedupAnnouncements_cons]
      unfold insertCanonical
      by_cases hany : (dedupAnnouncements bs).any (sameScid b) = true
      · rw [ite_eq_left hany]
        exact ih
      · rw [ite_eq_right hany]
        have hanyf : (dedupAnnouncements bs).any (sameScid b) = false := by
          cases h : (dedupAnnouncements bs).any (sameScid b) <;> simp_all
        have hpoint : ∀ x ∈ dedupAnnouncements bs, sameScid b x = false := by
          intro x hx
          have hx' := (List.any_eq_false
            (l := dedupAnnouncements bs) (p := sameScid b)).mp hanyf x hx
          simpa using hx'
        intro x hx y hy hscid
        rw [List.mem_cons] at hx hy
        rcases hx with hxb | hxd <;> rcases hy with hyb | hyd
        · rw [hxb, hyb]
        · rw [hxb] at hscid ⊢
          have hfalse := hpoint y hyd
          have htrue : sameScid b y = true := by
            simp [sameScid, hscid]
          rw [htrue] at hfalse
          exact Bool.noConfusion hfalse
        · rw [hyb] at hscid ⊢
          have hfalse := hpoint x hxd
          have htrue : sameScid b x = true := by
            simp [sameScid, hscid.symm]
          rw [htrue] at hfalse
          exact Bool.noConfusion hfalse
        · exact ih x hxd y hyd hscid

/-- **Deduplication is semantics-preserving under the canonical invariant.**
If the input has no conflicting same-channel records, the canonical view keeps
exactly its announcement members. -/
theorem mem_dedupAnnouncements_of_canonical {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (hc : CanonicalAnnouncements l) (ha : a ∈ l) :
    a ∈ dedupAnnouncements l := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      rw [dedupAnnouncements_cons]
      have hcbs : CanonicalAnnouncements bs := by
        intro x hx y hy h
        exact hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) h
      rcases List.mem_cons.mp ha with hb | ha
      · rw [hb]
        unfold insertCanonical
        by_cases hany : (dedupAnnouncements bs).any (sameScid b) = true
        · rw [ite_eq_left hany]
          rcases (List.any_eq_true
            (l := dedupAnnouncements bs) (p := sameScid b)).mp hany with
            ⟨x, hx, hsame⟩
          have hxbs : x ∈ bs := mem_of_mem_dedupAnnouncements hx
          have hscid : b.shortChannelId = x.shortChannelId :=
            (sameScid_eq_true_iff b x).mp hsame
          have hbx : b = x :=
            hc b (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hxbs) hscid
          rw [hbx]
          exact hx
        · rw [ite_eq_right hany]
          exact List.mem_cons_self ..
      · exact mem_insertCanonical_of_mem (ih hcbs ha)

namespace GossipState

/-- The store-level canonical-invariant spelling. -/
def Canonical (s : GossipState) : Prop :=
  CanonicalAnnouncements s.announcements

/-- **Canonical store view.**  The same store with announcements deduplicated
by `short_channel_id`.  Update and node-announcement lists are untouched, so
this is a viewing operation, not a gossip transition. -/
def canonicalView (s : GossipState) : GossipState :=
  { s with announcements := dedupAnnouncements s.announcements }

/-- The canonical view's announcement list is the deduplicated list. -/
@[simp] theorem canonicalView_announcements (s : GossipState) :
    s.canonicalView.announcements = dedupAnnouncements s.announcements :=
  rfl

/-- The canonical view always satisfies the canonical invariant. -/
theorem canonicalView_canonical (s : GossipState) : s.canonicalView.Canonical :=
  canonical_dedupAnnouncements s.announcements

/-- Under the canonical invariant, deduplication preserves ordinary key
attribution exactly. -/
theorem updateKeyAnnounced_canonicalView (s : GossipState) (u : ChannelUpdate)
    (hc : s.Canonical) :
    s.canonicalView.updateKeyAnnounced u ↔ s.updateKeyAnnounced u := by
  constructor
  · rintro ⟨a, ha, hscid, hkey⟩
    exact ⟨a, mem_of_mem_dedupAnnouncements ha, hscid, hkey⟩
  · rintro ⟨a, ha, hscid, hkey⟩
    exact ⟨a, mem_dedupAnnouncements_of_canonical hc ha, hscid, hkey⟩

/-- Under the canonical invariant, deduplication preserves direction-keyed
attribution exactly.  This is the store-view justification for using
`canonicalView` in the endpoint theorem. -/
theorem updateKeyAnnouncedDirectional_canonicalView (s : GossipState)
    (u : ChannelUpdate) (hc : s.Canonical) :
    s.canonicalView.updateKeyAnnouncedDirectional u ↔
      s.updateKeyAnnouncedDirectional u := by
  constructor
  · rintro ⟨a, ha, hscid, hkey⟩
    exact ⟨a, mem_of_mem_dedupAnnouncements ha, hscid, hkey⟩
  · rintro ⟨a, ha, hscid, hkey⟩
    exact ⟨a, mem_dedupAnnouncements_of_canonical hc ha, hscid, hkey⟩

end GossipState

/-! ## Canonical announcement replacement, node-key registration, and
canonical update supersession (additive, `RT-02`, wave 6)

The wave-5 canonical *view* (`dedupAnnouncements`, `GossipState.canonicalView`)
removes same-`short_channel_id` duplicates but is not a transition: raw
`applyGossip` remains append-only, and `NodeKeyConsistent` remains an explicit
hypothesis.  This section supplies the store-level primitives needed by a
*transition* that maintains both invariants by construction:

* `insertReplacing` replaces the stored announcement for the incoming
  `short_channel_id` instead of appending.  It is the announcement half of the
  canonicalising store step.
* `GossipState.CompatibleWithStore` is the node-key registration gate: an
  incoming announcement must not rebind a graph node that is already bound to
  a different BOLT 7 key.
* `bindNodeKeys` records the incoming announcement's two `NodeId → PubKey`
  bindings; `NodeKeyAgreement` is the list-level form of
  `GossipState.NodeKeyConsistent`.
* `rotateNodeKey` and `rekeyAnnouncement` model an explicit key rotation: the
  registration map and every affected announcement field are rewritten
  together.  Rotation is a registration operation only; it does not preserve
  announcement signature validity (the re-signed records are the caller's
  obligation), which is stated in the wave-6 proof module.
* `insertUpdateCanonical` replaces the stored update for the same
  `(short_channel_id, direction)` slot when a strictly newer update arrives;
  `UpdateSupersedes` is the BOLT 7 timestamp gate for that replacement.

Nothing below changes `applyGossip`, `GossipState.applyUpdate`,
`applyUpdateAttributed`, `applyUpdateDirected`, `dedupAnnouncements`, or any
existing statement.  The raw store stays append-only, signature-unfiltered,
and undeduplicated. -/

/-- **Replace-by-channel insertion.**  Drop every stored announcement for the
incoming `short_channel_id`, then prepend the incoming one.  Under the
canonical invariant this is an ordinary supersession; without it, it is the
canonicalising replacement the wave-5 `insertCanonical` deliberately did not
perform on the raw store. -/
def insertReplacing (a : ChannelAnnellation)
    (l : List ChannelAnnellation) : List ChannelAnnellation :=
  a :: l.filter (fun b => decide (b.shortChannelId ≠ a.shortChannelId))

/-- **Exact membership after replacement.**  An announcement is stored iff it
is the incoming one, or it was stored before with a different
`short_channel_id`. -/
theorem mem_insertReplacing_iff {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} :
    b ∈ insertReplacing a l ↔
      b = a ∨ (b ∈ l ∧ b.shortChannelId ≠ a.shortChannelId) := by
  simp [insertReplacing, List.mem_filter]

/-- A stored announcement for a different channel survives replacement. -/
theorem mem_insertReplacing_of_mem_of_ne {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (hb : b ∈ l)
    (hne : b.shortChannelId ≠ a.shortChannelId) :
    b ∈ insertReplacing a l :=
  List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hb, decide_eq_true hne⟩)

/-- Every non-incoming member after replacement was stored before. -/
theorem mem_of_mem_insertReplacing_of_ne {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : b ∈ insertReplacing a l)
    (hne : b ≠ a) : b ∈ l := by
  rcases mem_insertReplacing_iff.mp h with rfl | ⟨hb, _⟩
  · exact absurd rfl hne
  · exact hb

/-- **Replacement preserves canonicality.**  A canonical list stays canonical
after replacing a channel's record: the old record for that channel is
removed, so exactly one record per `short_channel_id` remains. -/
theorem canonical_insertReplacing {l : List ChannelAnnellation}
    (hc : CanonicalAnnouncements l) (a : ChannelAnnellation) :
    CanonicalAnnouncements (insertReplacing a l) := by
  intro x hx y hy hscid
  rcases mem_insertReplacing_iff.mp hx with rfl | ⟨hxl, hxn⟩
  · rcases mem_insertReplacing_iff.mp hy with rfl | ⟨hyl, hyn⟩
    · rfl
    · exact absurd hscid.symm hyn
  · rcases mem_insertReplacing_iff.mp hy with rfl | ⟨hyl, hyn⟩
    · exact absurd hscid hxn
    · exact hc x hxl y hyl hscid

namespace GossipState

/-- **Node-key registration compatibility.**  The incoming announcement does
not rebind any graph node already named by a stored announcement to a different
BOLT 7 key.  The four implications cover both endpoint positions of the
incoming announcement against both positions of every stored one.  This is the
admission check that makes `NodeKeyConsistent` a transition invariant rather
than a hypothesis. -/
def CompatibleWithStore (s : GossipState) (a : ChannelAnnellation) : Prop :=
  ∀ b ∈ s.announcements,
    (b.node1 = a.node1 → b.nodeKey1 = a.nodeKey1) ∧
    (b.node2 = a.node1 → b.nodeKey2 = a.nodeKey1) ∧
    (b.node1 = a.node2 → b.nodeKey1 = a.nodeKey2) ∧
    (b.node2 = a.node2 → b.nodeKey2 = a.nodeKey2)

end GossipState

/-- **List-level node-key agreement.**  This is `NodeKeyConsistent` unfolded
to an announcement list, so the registration lemmas can be stated without
constructing a store. -/
def NodeKeyAgreement (nodeKeyOf : NodeId → PubKey)
    (l : List ChannelAnnellation) : Prop :=
  ∀ a ∈ l, nodeKeyOf a.node1 = a.nodeKey1 ∧
    nodeKeyOf a.node2 = a.nodeKey2

/-- `NodeKeyConsistent` is exactly `NodeKeyAgreement` on the announcement
list. -/
theorem nodeKeyConsistent_iff_agreement (nodeKeyOf : NodeId → PubKey)
    (s : GossipState) :
    GossipState.NodeKeyConsistent nodeKeyOf s ↔
      NodeKeyAgreement nodeKeyOf s.announcements :=
  Iff.rfl

/-- **Bind an announcement's two graph nodes to its BOLT 7 keys.**  The
registration map is total; nodes not named by the announcement keep their
previous binding. -/
def bindNodeKeys (nodeKeyOf : NodeId → PubKey) (a : ChannelAnnellation) :
    NodeId → PubKey :=
  fun n => if n = a.node1 then a.nodeKey1
    else if n = a.node2 then a.nodeKey2 else nodeKeyOf n

/-- The first endpoint is bound to `nodeKey1`. -/
@[simp] theorem bindNodeKeys_node1 (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) :
    bindNodeKeys nodeKeyOf a a.node1 = a.nodeKey1 := by
  simp [bindNodeKeys]

/-- The second endpoint is bound to `nodeKey2`, provided the endpoints are
distinct.  BOLT 7 requires distinct channel endpoints; the distinctness is an
explicit admission hypothesis, not a hidden field invariant. -/
theorem bindNodeKeys_node2 (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) (h : a.node1 ≠ a.node2) :
    bindNodeKeys nodeKeyOf a a.node2 = a.nodeKey2 := by
  simp [bindNodeKeys, Ne.symm h]

/-- A node not named by the announcement keeps its old binding. -/
theorem bindNodeKeys_of_ne (nodeKeyOf : NodeId → PubKey)
    (a : ChannelAnnellation) {n : NodeId} (h1 : n ≠ a.node1)
    (h2 : n ≠ a.node2) :
    bindNodeKeys nodeKeyOf a n = nodeKeyOf n := by
  simp [bindNodeKeys, h1, h2]

/-- **Registration establishes node-key consistency.**  If the store is
consistent, the incoming announcement is compatible with every stored
announcement, and its endpoints are distinct, then binding its two nodes and
replacing its channel record keeps `NodeKeyAgreement` for the resulting
announcement list. -/
theorem nodeKeyAgreement_insertReplacing {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} {a : ChannelAnnellation}
    (hc : NodeKeyAgreement nodeKeyOf s.announcements)
    (hcompat : s.CompatibleWithStore a)
    (hne : a.node1 ≠ a.node2) :
    NodeKeyAgreement (bindNodeKeys nodeKeyOf a)
      (insertReplacing a s.announcements) := by
  intro b hb
  rcases mem_insertReplacing_iff.mp hb with hba | ⟨hb, _hbne⟩
  · subst b
    exact ⟨bindNodeKeys_node1 nodeKeyOf a,
      bindNodeKeys_node2 nodeKeyOf a hne⟩
  · rcases hc b hb with ⟨hb1, hb2⟩
    rcases hcompat b hb with ⟨hc1, hc2, hc3, hc4⟩
    constructor
    · by_cases h1 : b.node1 = a.node1
      · rw [h1, bindNodeKeys_node1]
        exact (hc1 h1).symm
      · by_cases h2 : b.node1 = a.node2
        · rw [h2, bindNodeKeys_node2 nodeKeyOf a hne]
          exact (hc3 h2).symm
        · rw [bindNodeKeys_of_ne nodeKeyOf a h1 h2]
          exact hb1
    · by_cases h1 : b.node2 = a.node1
      · rw [h1, bindNodeKeys_node1]
        exact (hc2 h1).symm
      · by_cases h2 : b.node2 = a.node2
        · rw [h2, bindNodeKeys_node2 nodeKeyOf a hne]
          exact (hc4 h2).symm
        · rw [bindNodeKeys_of_ne nodeKeyOf a h1 h2]
          exact hb2

/-- Store-level form of `nodeKeyAgreement_insertReplacing`. -/
theorem nodeKeyConsistent_insertReplacing {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} {a : ChannelAnnellation}
    (hc : GossipState.NodeKeyConsistent nodeKeyOf s)
    (hcompat : s.CompatibleWithStore a)
    (hne : a.node1 ≠ a.node2) :
    GossipState.NodeKeyConsistent (bindNodeKeys nodeKeyOf a)
      { s with announcements := insertReplacing a s.announcements } :=
  nodeKeyAgreement_insertReplacing hc hcompat hne

/-! ### Explicit node-key rotation -/

/-- **Rotate one graph node's registered BOLT 7 key.** -/
def rotateNodeKey (nodeKeyOf : NodeId → PubKey) (n : NodeId) (k : PubKey) :
    NodeId → PubKey :=
  fun m => if m = n then k else nodeKeyOf m

/-- **Rewrite an announcement to a rotated key.**  Only the fields naming the
rotated graph node change; the announcement's identity, endpoints, capacity,
digest, and signatures are untouched.  A production rotation must re-sign the
record; this operation models the key-registration half only. -/
def rekeyAnnouncement (a : ChannelAnnellation) (n : NodeId) (k : PubKey) :
    ChannelAnnellation :=
  { a with
    nodeKey1 := if a.node1 = n then k else a.nodeKey1
    nodeKey2 := if a.node2 = n then k else a.nodeKey2 }

@[simp] theorem rekeyAnnouncement_shortChannelId (a : ChannelAnnellation)
    (n : NodeId) (k : PubKey) :
    (rekeyAnnouncement a n k).shortChannelId = a.shortChannelId := rfl

@[simp] theorem rekeyAnnouncement_node1 (a : ChannelAnnellation)
    (n : NodeId) (k : PubKey) :
    (rekeyAnnouncement a n k).node1 = a.node1 := rfl

@[simp] theorem rekeyAnnouncement_node2 (a : ChannelAnnellation)
    (n : NodeId) (k : PubKey) :
    (rekeyAnnouncement a n k).node2 = a.node2 := rfl

/-- **Rewrite an announcement list to a rotated key.** -/
def rekeyAnnouncements (l : List ChannelAnnellation) (n : NodeId)
    (k : PubKey) : List ChannelAnnellation :=
  l.map (fun a => rekeyAnnouncement a n k)

/-- **Rewrite a store's announcement list to a rotated key.**  Updates, node
announcements, and the registration map are untouched. -/
def rekeyStore (s : GossipState) (n : NodeId) (k : PubKey) : GossipState :=
  { s with announcements := rekeyAnnouncements s.announcements n k }

@[simp] theorem rekeyStore_announcements (s : GossipState) (n : NodeId)
    (k : PubKey) :
    (rekeyStore s n k).announcements = rekeyAnnouncements s.announcements n k :=
  rfl

/-- **Rotation preserves node-key consistency** when every announcement is
rekeyed alongside the registration map.  This is a purely registration-level
result: announcement signatures are *not* preserved and must be regenerated by
the caller. -/
theorem nodeKeyConsistent_rekey {nodeKeyOf : NodeId → PubKey}
    {s : GossipState} (h : GossipState.NodeKeyConsistent nodeKeyOf s)
    (n : NodeId) (k : PubKey) :
    GossipState.NodeKeyConsistent (rotateNodeKey nodeKeyOf n k)
      (rekeyStore s n k) := by
  intro a' ha'
  rw [rekeyStore_announcements, rekeyAnnouncements] at ha'
  rcases List.mem_map.mp ha' with ⟨a, ha, rfl⟩
  rcases h a ha with ⟨h1, h2⟩
  constructor
  · by_cases hn : a.node1 = n
    · simp [rotateNodeKey, rekeyAnnouncement, hn]
    · simp [rotateNodeKey, rekeyAnnouncement, hn, h1]
  · by_cases hn : a.node2 = n
    · simp [rotateNodeKey, rekeyAnnouncement, hn]
    · simp [rotateNodeKey, rekeyAnnouncement, hn, h2]

/-- Rotation preserves canonicality: rewriting keys does not change the
`short_channel_id` of any record. -/
theorem canonical_rekey {l : List ChannelAnnellation}
    (hc : CanonicalAnnouncements l) (n : NodeId) (k : PubKey) :
    CanonicalAnnouncements (rekeyAnnouncements l n k) := by
  intro x hx y hy hscid
  rw [rekeyAnnouncements] at hx hy
  rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
  have hscid' : a.shortChannelId = b.shortChannelId := hscid
  rw [hc a ha b hb hscid']

/-! ### Canonical update supersession -/

/-- **BOLT 7 supersession gate for one directional slot.**  Every stored update
for the incoming update's `(short_channel_id, direction)` is strictly older.
Updates for other channels or the reverse direction are unaffected. -/
def UpdateSupersedes (u : ChannelUpdate) (l : List ChannelUpdate) : Prop :=
  ∀ v ∈ l, v.shortChannelId = u.shortChannelId → v.direction = u.direction →
    v.timestamp < u.timestamp

/-- **Replace-by-slot update insertion.**  Remove every stored update for the
incoming `(short_channel_id, direction)` slot and prepend the incoming update.
Unlike the raw `GossipState.applyUpdate`, this keeps at most one update per
directional slot. -/
def insertUpdateCanonical (u : ChannelUpdate) (l : List ChannelUpdate) :
    List ChannelUpdate :=
  u :: l.filter (fun v => decide (¬ (v.shortChannelId = u.shortChannelId ∧
    v.direction = u.direction)))

/-- **Exact membership after canonical update insertion.** -/
theorem mem_insertUpdateCanonical_iff {u v : ChannelUpdate}
    {l : List ChannelUpdate} :
    v ∈ insertUpdateCanonical u l ↔
      v = u ∨ (v ∈ l ∧ (v.shortChannelId ≠ u.shortChannelId ∨
        v.direction ≠ u.direction)) := by
  constructor
  · intro hv
    rcases List.mem_cons.mp hv with hvu | hvf
    · exact Or.inl hvu
    · have hf := List.mem_filter.mp hvf
      refine Or.inr ⟨hf.1, ?_⟩
      have hnot : ¬ (v.shortChannelId = u.shortChannelId ∧
          v.direction = u.direction) := of_decide_eq_true hf.2
      by_cases hA : v.shortChannelId = u.shortChannelId
      · by_cases hB : v.direction = u.direction
        · exact absurd ⟨hA, hB⟩ hnot
        · exact Or.inr hB
      · exact Or.inl hA
  · intro hv
    rcases hv with hvu | ⟨hvl, hne⟩
    · subst v
      exact List.mem_cons_self ..
    · refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hvl, ?_⟩)
      apply decide_eq_true
      rintro ⟨hA, hB⟩
      rcases hne with hA' | hB'
      · exact hA' hA
      · exact hB' hB

/-- **Canonical update insertion leaves one update per directional slot.**
Every stored update in the incoming slot is the incoming update itself. -/
theorem insertUpdateCanonical_slot_unique (u : ChannelUpdate)
    (l : List ChannelUpdate) :
    ∀ v ∈ insertUpdateCanonical u l,
      v.shortChannelId = u.shortChannelId → v.direction = u.direction → v = u := by
  intro v hv hscid hdir
  rcases mem_insertUpdateCanonical_iff.mp hv with hvu | ⟨_hvl, hne⟩
  · exact hvu
  · rcases hne with hscid' | hdir'
    · exact absurd hscid hscid'
    · exact absurd hdir hdir'

/-- Under the supersession gate, the incoming update is the newest record in
its directional slot. -/
theorem insertUpdateCanonical_newest {u : ChannelUpdate}
    {l : List ChannelUpdate} (_h : UpdateSupersedes u l) :
    ∀ v ∈ insertUpdateCanonical u l,
      v.shortChannelId = u.shortChannelId → v.direction = u.direction →
        v.timestamp ≤ u.timestamp := by
  intro v hv hscid hdir
  have hvu : v = u := insertUpdateCanonical_slot_unique u l v hv hscid hdir
  rw [hvu]
  exact Nat.le_refl u.timestamp

/-! ## Replacement removals and their accounting (additive, `RT-01`, wave 8)

`insertReplacing` and `insertUpdateCanonical` drop the stored records they
replace.  The definitions below make those removals explicit, so an epoch or
history layer can record *what* a replacement superseded instead of only the
resulting store.  They are list primitives: nothing here changes a transition.
-/

/-- **Stored announcements removed by `insertReplacing a`.**  These are exactly
the old records for the incoming `short_channel_id`.  Under the canonical
invariant there is at most one such record; on the raw store there may be
several. -/
def replacedAnnouncements (a : ChannelAnnellation)
    (l : List ChannelAnnellation) : List ChannelAnnellation :=
  l.filter (fun b => decide (b.shortChannelId = a.shortChannelId))

/-- Exact membership in the removed announcement list. -/
theorem mem_replacedAnnouncements_iff {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} :
    b ∈ replacedAnnouncements a l ↔
      b ∈ l ∧ b.shortChannelId = a.shortChannelId := by
  simp [replacedAnnouncements]

/-- Every removed announcement was an old record for the incoming channel. -/
theorem mem_replacedAnnouncements_of_mem {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (hb : b ∈ replacedAnnouncements a l) :
    b ∈ l ∧ b.shortChannelId = a.shortChannelId :=
  mem_replacedAnnouncements_iff.mp hb

/-- A replacement removes a record exactly when it is a same-channel old
record.  This is the accounting law for announcement replacement: for any
record other than the incoming one, surviving and being listed as replaced are
exact complements. -/
theorem mem_insertReplacing_iff_not_replaced {a b : ChannelAnnellation}
    {l : List ChannelAnnellation} (hne : b ≠ a) :
    b ∈ insertReplacing a l ↔
      b ∈ l ∧ b ∉ replacedAnnouncements a l := by
  rw [mem_insertReplacing_iff]
  constructor
  · rintro (hba | ⟨hbl, hbne⟩)
    · exact absurd hba hne
    · refine ⟨hbl, ?_⟩
      intro hbr
      exact hbne (mem_replacedAnnouncements_iff.mp hbr).2
  · rintro ⟨hbl, hbr⟩
    refine Or.inr ⟨hbl, ?_⟩
    intro hsame
    exact hbr (mem_replacedAnnouncements_iff.mpr ⟨hbl, hsame⟩)

/-- The removed announcement list is duplicate-free when the input is. -/
theorem replacedAnnouncements_nodup {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : l.Nodup) :
    (replacedAnnouncements a l).Nodup :=
  h.filter _

/-- **At most one replacement per channel under canonicality.**  In a
canonical announcement list, every two records removed by one replacement are
the same record. -/
theorem replacedAnnouncements_subsingleton {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (hc : CanonicalAnnouncements l) :
    ∀ x ∈ replacedAnnouncements a l,
      ∀ y ∈ replacedAnnouncements a l, x = y := by
  intro x hx y hy
  rcases mem_replacedAnnouncements_iff.mp hx with ⟨hxl, hxs⟩
  rcases mem_replacedAnnouncements_iff.mp hy with ⟨hyl, hys⟩
  exact hc x hxl y hyl (hxs.trans hys.symm)

/-- The removed announcement list is empty exactly when no stored record
addresses the incoming channel. -/
theorem replacedAnnouncements_eq_nil_iff {a : ChannelAnnellation}
    {l : List ChannelAnnellation} :
    replacedAnnouncements a l = [] ↔
      ∀ b ∈ l, b.shortChannelId ≠ a.shortChannelId := by
  constructor
  · intro h b hb hsame
    have hmem : b ∈ replacedAnnouncements a l :=
      mem_replacedAnnouncements_iff.mpr ⟨hb, hsame⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro b hb
    exact h b (mem_replacedAnnouncements_iff.mp hb).1
      (mem_replacedAnnouncements_iff.mp hb).2

/-- **Stored updates removed by `insertUpdateCanonical u`.**  These are exactly
the old records in the incoming `(short_channel_id, direction)` slot. -/
def replacedUpdates (u : ChannelUpdate)
    (l : List ChannelUpdate) : List ChannelUpdate :=
  l.filter (fun v => decide (v.shortChannelId = u.shortChannelId ∧
    v.direction = u.direction))

/-- Exact membership in the removed update list. -/
theorem mem_replacedUpdates_iff {u v : ChannelUpdate}
    {l : List ChannelUpdate} :
    v ∈ replacedUpdates u l ↔
      v ∈ l ∧ v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction := by
  simp [replacedUpdates]

/-- Every removed update was an old record in the incoming directional slot. -/
theorem mem_replacedUpdates_of_mem {u v : ChannelUpdate}
    {l : List ChannelUpdate} (hv : v ∈ replacedUpdates u l) :
    v ∈ l ∧ v.shortChannelId = u.shortChannelId ∧
      v.direction = u.direction :=
  mem_replacedUpdates_iff.mp hv

/-- The removal history records the supersession direction: under the BOLT 7
per-slot gate, every replaced update is strictly older than the incoming one. -/
theorem replacedUpdates_timestamp_lt {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : UpdateSupersedes u l) :
    ∀ v ∈ replacedUpdates u l, v.timestamp < u.timestamp := by
  intro v hv
  rcases mem_replacedUpdates_iff.mp hv with ⟨hvl, hscid, hdir⟩
  exact h v hvl hscid hdir

/-- A slot update removes a record exactly when it is a same-slot old record. -/
theorem mem_insertUpdateCanonical_iff_not_replaced {u v : ChannelUpdate}
    {l : List ChannelUpdate} (hne : v ≠ u) :
    v ∈ insertUpdateCanonical u l ↔
      v ∈ l ∧ v ∉ replacedUpdates u l := by
  rw [mem_insertUpdateCanonical_iff]
  constructor
  · rintro (hvu | ⟨hvl, hne'⟩)
    · exact absurd hvu hne
    · refine ⟨hvl, ?_⟩
      intro hvr
      rcases mem_replacedUpdates_iff.mp hvr with ⟨_, hscid, hdir⟩
      rcases hne' with hscid' | hdir'
      · exact hscid' hscid
      · exact hdir' hdir
  · rintro ⟨hvl, hvr⟩
    refine Or.inr ⟨hvl, ?_⟩
    have hnot : ¬ (v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction) := by
      intro hsame
      exact hvr (mem_replacedUpdates_iff.mpr ⟨hvl, hsame.1, hsame.2⟩)
    by_cases hscid : v.shortChannelId = u.shortChannelId
    · by_cases hdir : v.direction = u.direction
      · exact absurd ⟨hscid, hdir⟩ hnot
      · exact Or.inr hdir
    · exact Or.inl hscid

/-- The removed update list is duplicate-free when the input is. -/
theorem replacedUpdates_nodup {u : ChannelUpdate} {l : List ChannelUpdate}
    (h : l.Nodup) : (replacedUpdates u l).Nodup :=
  h.filter _

/-- The removed update list is empty exactly when no stored record addresses
the incoming directional slot. -/
theorem replacedUpdates_eq_nil_iff {u : ChannelUpdate}
    {l : List ChannelUpdate} :
    replacedUpdates u l = [] ↔
      ∀ v ∈ l, ¬ (v.shortChannelId = u.shortChannelId ∧
        v.direction = u.direction) := by
  constructor
  · intro h v hv hsame
    have hmem : v ∈ replacedUpdates u l :=
      mem_replacedUpdates_iff.mpr ⟨hv, hsame.1, hsame.2⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    rw [List.eq_nil_iff_forall_not_mem]
    intro v hv
    rcases mem_replacedUpdates_iff.mp hv with ⟨hvl, hscid, hdir⟩
    exact h v hvl ⟨hscid, hdir⟩

/-! ## Canonical selection of a raw store (additive, `RT-01`, wave 7)

`applyGossip` is append-only: it never replaces an announcement for an existing
`short_channel_id` and never replaces a `channel_update` slot.  The wave-6
transition `admitGossipCanonical` (in
`LnLean.Proofs.Routing.GossipCanonicalTargets`) therefore does not refine raw
insertion as a *function*: raw insertion has no signature gate, no node-key
registration gate, and no per-direction slot replacement.

This section adds the store-level primitives needed to state the sharpest true
relation between the two paths:

* `UpdatesSlotUnique` is the raw-store shape invariant "at most one update per
  `(short_channel_id, direction)` slot".  Raw insertion does **not** maintain it
  (a newer update is appended next to the older one); the canonical transition
  does (`insertUpdateCanonical`).
* `selectAnnouncements` keeps the **head-most** (newest) record for each
  `short_channel_id`; `selectUpdates` keeps the head-most record for each
  direction slot.  These are the canonical *observations* of a raw store: they
  replace instead of append and therefore have the canonical shape by
  construction.
* `canonicalStoreView` applies both selectors to a store without changing its
  node announcements.
* The three `canonicalStoreView_applyGossip_*` theorems are the refinement
  square: observing a raw step is the same as applying the canonical *shape*
  operation (`insertReplacing`, `insertUpdateCanonical`) to the observation.
  The admission gates (signature, attribution, registration) are exactly what
  raw insertion lacks; the wave-7 proof module adds them and proves the
  agreement theorem on the common domain.

Nothing above changes any existing definition or theorem.  In particular
`applyGossip`, `GossipState.applyUpdate`, `canonicalView`
(`dedupAnnouncements`, oldest-record-wins), and every wave-A/5/6 statement keep
their exact meaning. -/

/-- **At most one stored update per `(short_channel_id, direction)` slot.**

This is the per-slot shape invariant of a production BOLT 7 store.  The raw
store does not maintain it: `GossipState.applyUpdate` only compares the single
global timestamp clock, so a newer update for one direction is appended next to
the older update for that direction. -/
def UpdatesSlotUnique (l : List ChannelUpdate) : Prop :=
  ∀ u ∈ l, ∀ v ∈ l, u.shortChannelId = v.shortChannelId →
    u.direction = v.direction → u = v

/-- The empty update list has no slot collisions. -/
theorem updatesSlotUnique_nil : UpdatesSlotUnique [] := by
  intro u hu
  simp at hu

/-- **Canonical slot insertion preserves slot uniqueness.**  The deleted
records are exactly the incoming slot, and at most one record remains there. -/
theorem updatesSlotUnique_insertUpdateCanonical {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : UpdatesSlotUnique l) :
    UpdatesSlotUnique (insertUpdateCanonical u l) := by
  intro x hx y hy hscid hdir
  rcases mem_insertUpdateCanonical_iff.mp hx with rfl | ⟨hxl, hxne⟩
  · rcases mem_insertUpdateCanonical_iff.mp hy with rfl | ⟨hyl, hyne⟩
    · rfl
    · rcases hyne with hs | hd
      · exact absurd hscid.symm hs
      · exact absurd hdir.symm hd
  · rcases mem_insertUpdateCanonical_iff.mp hy with rfl | ⟨hyl, hyne⟩
    · rcases hxne with hs | hd
      · exact absurd hscid hs
      · exact absurd hdir hd
    · exact h x hxl y hyl hscid hdir

/-- **Canonical update selection.**  Keep the head-most record for each
`(short_channel_id, direction)` slot.  Because gossip lists are stored
newest-first, the head-most record is the newest one; the wave-7 report records
that raw-reachable stores are timestamp-decreasing and that the selector is
therefore "newest wins" on them. -/
def selectUpdates : List ChannelUpdate → List ChannelUpdate
  | [] => []
  | u :: l => insertUpdateCanonical u (selectUpdates l)

@[simp] theorem selectUpdates_nil : selectUpdates [] = [] := rfl

/-- Unfolding of the update selector at a cons. -/
theorem selectUpdates_cons (u : ChannelUpdate) (l : List ChannelUpdate) :
    selectUpdates (u :: l) = insertUpdateCanonical u (selectUpdates l) := rfl

/-- The selected update list has at most one record per directional slot. -/
theorem updatesSlotUnique_selectUpdates (l : List ChannelUpdate) :
    UpdatesSlotUnique (selectUpdates l) := by
  induction l with
  | nil => exact updatesSlotUnique_nil
  | cons u l ih => exact updatesSlotUnique_insertUpdateCanonical ih

/-- Selection removes updates; it never invents one. -/
theorem mem_selectUpdates {u : ChannelUpdate} {l : List ChannelUpdate}
    (h : u ∈ selectUpdates l) : u ∈ l := by
  induction l with
  | nil => simp [selectUpdates] at h
  | cons v l ih =>
      rw [selectUpdates_cons] at h
      rcases mem_insertUpdateCanonical_iff.mp h with hvu | ⟨hl, _⟩
      · rw [hvu]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hl)

/-- **Every raw slot survives selection.**  For every stored update there is a
selected update in the same `(short_channel_id, direction)` slot.  Selection
therefore does not lose a channel/direction, only redundant older records. -/
theorem exists_mem_selectUpdates_of_mem {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : u ∈ l) :
    ∃ v ∈ selectUpdates l, v.shortChannelId = u.shortChannelId ∧
      v.direction = u.direction := by
  induction l with
  | nil => simp at h
  | cons w l ih =>
      rw [selectUpdates_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨u, mem_insertUpdateCanonical_iff.mpr (Or.inl rfl), rfl, rfl⟩
      · rcases ih h with ⟨v, hv, hscid, hdir⟩
        by_cases h1 : v.shortChannelId = w.shortChannelId
        · by_cases h2 : v.direction = w.direction
          · exact ⟨w, mem_insertUpdateCanonical_iff.mpr (Or.inl rfl),
              h1.symm.trans hscid, h2.symm.trans hdir⟩
          · exact ⟨v, mem_insertUpdateCanonical_iff.mpr
              (Or.inr ⟨hv, Or.inr h2⟩), hscid, hdir⟩
        · exact ⟨v, mem_insertUpdateCanonical_iff.mpr
            (Or.inr ⟨hv, Or.inl h1⟩), hscid, hdir⟩

/-- The selected update list has no duplicate records. -/
theorem selectUpdates_nodup (l : List ChannelUpdate) :
    (selectUpdates l).Nodup := by
  induction l with
  | nil => simp [selectUpdates]
  | cons u l ih =>
      rw [selectUpdates_cons]
      unfold insertUpdateCanonical
      rw [List.nodup_cons]
      refine ⟨?_, List.Pairwise.filter _ ih⟩
      intro hmem
      rcases List.mem_filter.mp hmem with ⟨_, hdec⟩
      exact (of_decide_eq_true hdec) ⟨rfl, rfl⟩

/-- **Selection is the identity on a duplicate-free, slot-unique update
list.**  Such a list is already in canonical shape. -/
theorem selectUpdates_of_nodup_slotUnique {l : List ChannelUpdate}
    (hnd : l.Nodup) (hsu : UpdatesSlotUnique l) : selectUpdates l = l := by
  induction l with
  | nil => rfl
  | cons u l ih =>
      have hndl : l.Nodup := (List.nodup_cons.mp hnd).2
      have hnotmem : u ∉ l := (List.nodup_cons.mp hnd).1
      have hsul : UpdatesSlotUnique l := by
        intro x hx y hy hscid hdir
        exact hsu x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
          hscid hdir
      rw [selectUpdates_cons, ih hndl hsul]
      unfold insertUpdateCanonical
      rw [List.filter_eq_self.mpr]
      intro v hv
      apply decide_eq_true
      rintro ⟨hscid, hdir⟩
      have hvu : v = u :=
        hsu v (List.mem_cons_of_mem _ hv) u (List.mem_cons_self ..) hscid hdir
      exact hnotmem (hvu ▸ hv)

/-- **Update selection is idempotent.** -/
theorem selectUpdates_idempotent (l : List ChannelUpdate) :
    selectUpdates (selectUpdates l) = selectUpdates l :=
  selectUpdates_of_nodup_slotUnique (selectUpdates_nodup l)
    (updatesSlotUnique_selectUpdates l)

/-- **Canonical announcement selection.**  Keep the head-most (newest) record
for each `short_channel_id`.  This differs from `dedupAnnouncements`, which
keeps the *last* (oldest) occurrence; both are canonical in the
`CanonicalAnnouncements` sense, but only the head-most selector matches
`insertReplacing`, the canonical transition's announcement operation. -/
def selectAnnouncements : List ChannelAnnellation → List ChannelAnnellation
  | [] => []
  | a :: l => insertReplacing a (selectAnnouncements l)

@[simp] theorem selectAnnouncements_nil : selectAnnouncements [] = [] := rfl

/-- Unfolding of the announcement selector at a cons. -/
theorem selectAnnouncements_cons (a : ChannelAnnellation)
    (l : List ChannelAnnellation) :
    selectAnnouncements (a :: l) = insertReplacing a (selectAnnouncements l) :=
  rfl

/-- The selected announcement list has one record per `short_channel_id`. -/
theorem canonical_selectAnnouncements (l : List ChannelAnnellation) :
    CanonicalAnnouncements (selectAnnouncements l) := by
  induction l with
  | nil =>
      intro a ha
      simp [selectAnnouncements] at ha
  | cons a l ih =>
      rw [selectAnnouncements_cons]
      exact canonical_insertReplacing ih a

/-- Selection removes announcements; it never invents one. -/
theorem mem_selectAnnouncements {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : a ∈ selectAnnouncements l) : a ∈ l := by
  induction l with
  | nil => simp [selectAnnouncements] at h
  | cons b l ih =>
      rw [selectAnnouncements_cons] at h
      rcases mem_insertReplacing_iff.mp h with hba | ⟨hl, _⟩
      · rw [hba]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hl)

/-- **Every raw channel survives selection.**  For every stored announcement
there is a selected announcement with the same `short_channel_id`. -/
theorem exists_mem_selectAnnouncements_of_mem {a : ChannelAnnellation}
    {l : List ChannelAnnellation} (h : a ∈ l) :
    ∃ b ∈ selectAnnouncements l, b.shortChannelId = a.shortChannelId := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
      rw [selectAnnouncements_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨a, mem_insertReplacing_iff.mpr (Or.inl rfl), rfl⟩
      · rcases ih h with ⟨b, hb, hscid⟩
        by_cases hsame : b.shortChannelId = x.shortChannelId
        · exact ⟨x, mem_insertReplacing_iff.mpr (Or.inl rfl),
            hsame.symm.trans hscid⟩
        · exact ⟨b, mem_insertReplacing_of_mem_of_ne hb hsame, hscid⟩

/-- The selected announcement list has no duplicate records. -/
theorem selectAnnouncements_nodup (l : List ChannelAnnellation) :
    (selectAnnouncements l).Nodup := by
  induction l with
  | nil => simp [selectAnnouncements]
  | cons a l ih =>
      rw [selectAnnouncements_cons]
      unfold insertReplacing
      rw [List.nodup_cons]
      refine ⟨?_, List.Pairwise.filter _ ih⟩
      intro hmem
      rcases List.mem_filter.mp hmem with ⟨_, hdec⟩
      exact (of_decide_eq_true hdec) rfl

/-- **Selection is the identity on a duplicate-free canonical announcement
list.** -/
theorem selectAnnouncements_of_nodup_canonical {l : List ChannelAnnellation}
    (hnd : l.Nodup) (hc : CanonicalAnnouncements l) :
    selectAnnouncements l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have hndl : l.Nodup := (List.nodup_cons.mp hnd).2
      have hnotmem : a ∉ l := (List.nodup_cons.mp hnd).1
      have hcl : CanonicalAnnouncements l := by
        intro x hx y hy hscid
        exact hc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hscid
      rw [selectAnnouncements_cons, ih hndl hcl]
      unfold insertReplacing
      rw [List.filter_eq_self.mpr]
      intro b hb
      apply decide_eq_true
      intro hsame
      have hab : a = b :=
        hc a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) hsame.symm
      exact hnotmem (hab ▸ hb)

/-- **Announcement selection is idempotent.** -/
theorem selectAnnouncements_idempotent (l : List ChannelAnnellation) :
    selectAnnouncements (selectAnnouncements l) = selectAnnouncements l :=
  selectAnnouncements_of_nodup_canonical (selectAnnouncements_nodup l)
    (canonical_selectAnnouncements l)

/-- **Canonical observation of a raw store.**  Keep the newest announcement per
channel and the newest update per direction slot.  Node announcements are not
touched: node-record canonicalisation remains future work (see the `RT-02`
report). -/
def canonicalStoreView (s : GossipState) : GossipState :=
  { s with
    announcements := selectAnnouncements s.announcements
    updates := selectUpdates s.updates }

@[simp] theorem canonicalStoreView_announcements (s : GossipState) :
    (canonicalStoreView s).announcements = selectAnnouncements s.announcements :=
  rfl

@[simp] theorem canonicalStoreView_updates (s : GossipState) :
    (canonicalStoreView s).updates = selectUpdates s.updates :=
  rfl

@[simp] theorem canonicalStoreView_nodeAnnouncements (s : GossipState) :
    (canonicalStoreView s).nodeAnnouncements = s.nodeAnnouncements :=
  rfl

/-- The canonical observation always has one announcement per channel. -/
theorem canonicalStoreView_canonical (s : GossipState) :
    CanonicalAnnouncements (canonicalStoreView s).announcements :=
  canonical_selectAnnouncements s.announcements

/-- The canonical observation always has at most one update per direction
slot. -/
theorem canonicalStoreView_updates_slotUnique (s : GossipState) :
    UpdatesSlotUnique (canonicalStoreView s).updates :=
  updatesSlotUnique_selectUpdates s.updates

/-- The canonical observation is idempotent. -/
theorem canonicalStoreView_idempotent (s : GossipState) :
    canonicalStoreView (canonicalStoreView s) = canonicalStoreView s := by
  cases s with
  | mk ann upd node =>
      simp [canonicalStoreView, selectAnnouncements_idempotent,
        selectUpdates_idempotent]

/-- **A store already in canonical shape.**  Both selectors are the identity, so
the store already has one (newest) record per channel and per direction slot
and no duplicate records. -/
def CanonicalStoreShape (s : GossipState) : Prop :=
  selectAnnouncements s.announcements = s.announcements ∧
    selectUpdates s.updates = s.updates

/-- `canonicalStoreView` is the identity exactly on canonical-shaped stores. -/
theorem canonicalStoreView_eq_self_iff (s : GossipState) :
    canonicalStoreView s = s ↔ CanonicalStoreShape s := by
  cases s with
  | mk ann upd node =>
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [CanonicalStoreShape] using
            congrArg GossipState.announcements h
        · simpa [CanonicalStoreShape] using congrArg GossipState.updates h
      · rintro ⟨hann, hupd⟩
        simp [canonicalStoreView, hann, hupd]

/-- A raw store with duplicate-free canonical announcements and a duplicate-free
slot-unique update list is already in canonical shape. -/
theorem canonicalStoreShape_of_nodup {s : GossipState}
    (hc : CanonicalAnnouncements s.announcements)
    (hnda : s.announcements.Nodup)
    (hsu : UpdatesSlotUnique s.updates) (hndu : s.updates.Nodup) :
    CanonicalStoreShape s :=
  ⟨selectAnnouncements_of_nodup_canonical hnda hc,
    selectUpdates_of_nodup_slotUnique hndu hsu⟩

/-- **Refinement square, announcement branch.**  Observing a raw announcement
insertion is exactly the canonical replacement `insertReplacing` applied to the
observation.  No signature gate is needed for this *shape* law: the gates are
the separate admission conditions that raw insertion does not have. -/
theorem canonicalStoreView_applyGossip_announcements (s : GossipState)
    (a : ChannelAnnellation) :
    (canonicalStoreView (applyGossip s (.channelAnnouncement a))).announcements =
      insertReplacing a (canonicalStoreView s).announcements := by
  simp [canonicalStoreView, applyGossip, selectAnnouncements_cons]

/-- **Refinement square, update branch.**  Observing a raw update step is the
canonical slot insertion `insertUpdateCanonical` applied to the observation,
under the raw step's own global-clock test.  Note the test is `s`'s global
clock, not the canonical per-slot `UpdateSupersedes`; wave 7's proof module
shows that the canonical path can accept an update the raw clock ignores
(`canonical_admission_strictly_weaker_than_raw_clock`). -/
theorem canonicalStoreView_applyGossip_updates (s : GossipState)
    (u : ChannelUpdate) :
    (canonicalStoreView (applyGossip s (.channelUpdate u))).updates =
      if s.latestUpdateTimestamp < u.timestamp
        then insertUpdateCanonical u (canonicalStoreView s).updates
        else (canonicalStoreView s).updates := by
  by_cases h : s.latestUpdateTimestamp < u.timestamp
  · simp [canonicalStoreView, applyGossip, GossipState.applyUpdate, h,
      selectUpdates_cons]
  · simp [canonicalStoreView, applyGossip, GossipState.applyUpdate, h]

/-- **Refinement square, node-announcement branch.**  Node announcements are
appended by both paths and are not selected. -/
theorem canonicalStoreView_applyGossip_nodeAnnouncements (s : GossipState)
    (n : NodeAnnouncement) :
    (canonicalStoreView (applyGossip s (.nodeAnnouncement n))).nodeAnnouncements =
      n :: s.nodeAnnouncements :=
  rfl

/-- **At most one replacement per directional slot under slot uniqueness.**
In a slot-unique update list, every two records removed by one replacement are
the same record. -/
theorem replacedUpdates_subsingleton {u : ChannelUpdate}
    {l : List ChannelUpdate} (h : UpdatesSlotUnique l) :
    ∀ x ∈ replacedUpdates u l,
      ∀ y ∈ replacedUpdates u l, x = y := by
  intro x hx y hy
  rcases mem_replacedUpdates_iff.mp hx with ⟨hxl, hxs, hxd⟩
  rcases mem_replacedUpdates_iff.mp hy with ⟨hyl, hys, hyd⟩
  exact h x hxl y hyl (hxs.trans hys.symm) (hxd.trans hyd.symm)

end LnLean.Routing
