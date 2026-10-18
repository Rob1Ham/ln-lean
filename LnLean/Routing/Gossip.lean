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

end LnLean.Routing
