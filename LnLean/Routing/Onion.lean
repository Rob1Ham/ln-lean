import LnLean.Routing.Route

/-!
# LnLean.Routing.Onion

The BOLT 4 Sphinx onion at the interface level: packets, layers, peeling,
opening, and failure packets.

English claim of this module:

* `OnionPacket` is `(version, ephemeral_key, routing_info, layers, hmac)`;
  each `OnionLayer` carries one `OnionHop`, a ciphertext, and its HMAC.
* `sealLayer` prepends exactly one layer and `sealLayers` builds one layer
  per hop, so the layer count equals the hop count.
* `peel` never fails: with remaining layers it returns the head hop and the
  inner packet (forward), and with no layers it returns the terminal
  `routing_info` (final).  Terminal detection is therefore a structural
  test on the layer list, not a guess.
* `openLayer` accepts a layer only when the abstract HMAC verifier returns
  `true`; a successful open therefore *entails* HMAC verification.  This is
  the mechanical half of onion integrity.  The cryptographic half ("a
  successful HMAC cannot be forged") is the named assumption
  `OnionInterface.hmacBinding` (C8 in `docs/ASSUMPTIONS.md`) and is **not**
  proved here.
* Every layer contributes at least one byte to the encoded packet, hence
  `layers.length ≤ encodedSize`; a layer whose ciphertext fits the BOLT 4
  `hop_payloads` budget has bounded encoded size.
* A BOLT 4 failure packet pads the failure message to 256 bytes, adds a
  2-byte length prefix and a 32-byte HMAC, for 290 bytes total.

BOLT sections:

* BOLT 4, "Onion Routing" / "Packet Structure" (`version`, `ephemeral_key`,
  `hop_payloads`, `hmac`; the `hop_payloads` field is 1300 bytes and the
  packet is 1366 bytes).
* BOLT 4, "Payloads" (per-hop `short_channel_id`, `amt_to_forward`,
  `outgoing_cltv_value`; the final payload is distinguished by having no
  `short_channel_id`).
* BOLT 4, "Failure Messages" (`failure_message` 256 bytes, `failure_len`
  2 bytes, `um`/HMAC 32 bytes; packet 290 bytes).
* BOLT 4, "Onion Decryption" (peel one layer, check the HMAC, then either
  forward or deliver).

`rust-lightning` anchors (pinned commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`;
line numbers are anchored to the symbol, see `agents/reports/A6.md` for the
pin-verification caveat):

* `lightning/src/ln/onion_utils.rs:50` — `OnionPacket`, the wire packet
  (`version`, `public_key`, `hop_payloads`, `hmac`).
* `lightning/src/ln/onion_utils.rs:1050` — `build_onion_payloads` builds
  the per-hop payload list; the last one is the final payload.
* `lightning/src/ln/onion_utils.rs:1300` — `construct_onion_keys` /
  `encrypt_failure_packet` (Sphinx key derivation and error wrapping).
* `lightning/src/ln/onion_payment.rs:1` — `InboundOnionPayload`'s
  `Forward`/`Receive`/`ReceiveKeysend` split, the `OnionPayload` analogue.

What is **not** modelled:

* ChaCha20-Poly1305 encryption, HKDF key derivation, and the ECDH shared
  secret.  `ciphertext` is opaque and `sealLayer`/`openLayer` do not
  compute keys.
* Onion privacy, unlinkability, and the size-hiding property of the fixed
  `hop_payloads` field.  These are cryptographic claims, not structural
  ones.
* HMAC unforgeability.  Only the implication "accepted ⇒ verifier said
  `true`" is proved.
* BigSize/TLV encoding of the per-hop payload and the exact `hop_payloads`
  layout.  `routingInfo` and `ciphertext` are opaque byte arrays.
* Error *contents*: `OnionError` stores a code and data, not the BOLT 4
  failure-message TLV encoding; `packetSize` only proves the fixed padding
  arithmetic.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## BOLT 4 constants -/

/-- The BOLT 4 onion packet version modelled. -/
def ONION_VERSION : Nat := 0

/-- Length of the Sphinx HMAC (SHA-256 output). -/
def ONION_HMAC_LEN : Nat := 32

/-- Length of the `hop_payloads` field of a BOLT 4 packet. -/
def HOP_PAYLOADS_LEN : Nat := 1300

/-- Total BOLT 4 onion packet length: 1 + 33 + 1300 + 32. -/
def ONION_PACKET_LEN : Nat := 1 + 33 + HOP_PAYLOADS_LEN + ONION_HMAC_LEN

/-- Maximum size of one hop payload before its BigSize length prefix. -/
def MAX_HOP_PAYLOAD : Nat := HOP_PAYLOADS_LEN

/-- BOLT 4 failure-message padding target. -/
def ONION_ERROR_PAD : Nat := 256

/-- BOLT 4 failure-packet length prefix. -/
def ONION_ERROR_LEN_LEN : Nat := 2

/-- BOLT 4 failure-packet HMAC. -/
def ONION_ERROR_HMAC_LEN : Nat := 32

/-- Total BOLT 4 failure-packet length: 2 + 256 + 32. -/
def ONION_ERROR_PACKET_LEN : Nat :=
  ONION_ERROR_LEN_LEN + ONION_ERROR_PAD + ONION_ERROR_HMAC_LEN

theorem onion_packet_len_eq : ONION_PACKET_LEN = 1366 := by
  unfold ONION_PACKET_LEN
  rfl

theorem onion_error_packet_len_eq : ONION_ERROR_PACKET_LEN = 290 := by
  unfold ONION_ERROR_PACKET_LEN
  rfl

/-! ## Hops and layers -/

/-- The routing information carried by one onion layer.  This is the model
of BOLT 4's per-hop payload: the next channel, the amount to forward, and
the outgoing CLTV.  The actual TLV encoding (and BigSize lengths) is not
modelled. -/
structure OnionHop where
  node : NodeId
  shortChannelId : ShortChannelId
  amountMsat : Msat
  cltvDelta : Nat
deriving Repr, DecidableEq, BEq

/-- One encrypted onion layer: the hop it is addressed to, the ciphertext,
and the HMAC that authenticates the whole remaining packet. -/
structure OnionLayer where
  hop : OnionHop
  ciphertext : ByteArray
  hmac : ByteArray
deriving Repr, BEq

namespace OnionLayer

/-- Bytes contributed by a layer to the `hop_payloads` field, including the
one-byte marker that distinguishes an intermediate layer from the terminal
payload. -/
def encodedSize (l : OnionLayer) : Nat :=
  1 + l.ciphertext.size + l.hmac.size

/-- A layer whose ciphertext fits the hop-payload budget and whose HMAC is
32 bytes has bounded encoded size. -/
theorem encodedSize_bound (l : OnionLayer)
    (hc : l.ciphertext.size ≤ MAX_HOP_PAYLOAD)
    (hh : l.hmac.size = ONION_HMAC_LEN) :
    l.encodedSize ≤ MAX_HOP_PAYLOAD + 1 + ONION_HMAC_LEN := by
  unfold encodedSize
  omega

end OnionLayer

/-- A BOLT 4 Sphinx packet.  `layers` is outermost-first; `routingInfo` is
the terminal payload, returned by `peel` once `layers` is empty. -/
structure OnionPacket where
  version : Nat
  ephemeralKey : PubKey
  routingInfo : ByteArray
  layers : List OnionLayer
  hmac : ByteArray
deriving Repr, BEq

namespace OnionPacket

/-- Number of layers still sealed in the packet. -/
def layerCount (p : OnionPacket) : Nat := p.layers.length

/-- Structural size of the modelled packet: the terminal payload plus one
encoded-size contribution per layer plus a one-byte version marker. -/
def encodedSize (p : OnionPacket) : Nat :=
  p.routingInfo.size + (p.layers.map OnionLayer.encodedSize).sum + 1

/-- Fixed wire size of a packet whose `hop_payloads` field is the BOLT 4
1300-byte array.  This is a constant of the wire format, not a function of
the layer contents. -/
def wireSize (_ : OnionPacket) : Nat :=
  1 + 33 + HOP_PAYLOADS_LEN + ONION_HMAC_LEN

theorem wireSize_eq_ONION_PACKET_LEN (p : OnionPacket) :
    p.wireSize = ONION_PACKET_LEN := rfl

end OnionPacket

/-! ## Sealing -/

/-- Prepend one layer.  The version, ephemeral key, terminal payload, and
outer HMAC are carried over; the new layer's HMAC is the supplied tag. -/
def sealLayer (version : Nat) (ephemeralKey : PubKey) (hop : OnionHop)
    (ciphertext hmac : ByteArray) (inner : OnionPacket) : OnionPacket :=
  { version := version
    ephemeralKey := ephemeralKey
    routingInfo := inner.routingInfo
    layers := ⟨hop, ciphertext, hmac⟩ :: inner.layers
    hmac := inner.hmac }

/-- Seal one layer per hop, outermost first.  This is the structural part of
Sphinx construction; key derivation and encryption are abstracted away. -/
def sealLayers (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) : OnionPacket :=
  { version := version
    ephemeralKey := ephemeralKey
    routingInfo := payload
    layers := hops.map fun h => ⟨h, ByteArray.empty, ByteArray.empty⟩
    hmac := ByteArray.empty }

theorem sealLayer_layerCount (version : Nat) (ephemeralKey : PubKey)
    (hop : OnionHop) (ciphertext hmac : ByteArray) (inner : OnionPacket) :
    (sealLayer version ephemeralKey hop ciphertext hmac inner).layerCount =
      inner.layerCount + 1 := by
  simp [sealLayer, OnionPacket.layerCount]

/-- **Layer count equals hop count** for `sealLayers`. -/
theorem sealLayers_layerCount (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (sealLayers version ephemeralKey hops payload).layerCount = hops.length := by
  simp [sealLayers, OnionPacket.layerCount]

/-! ## Peeling and payloads -/

/-- The result of peeling one layer: either a forwarding instruction with
the remaining packet, or the terminal payload. -/
inductive OnionPayload where
  | forward (hop : OnionHop) (next : OnionPacket)
  | final (payload : ByteArray)
deriving Repr, BEq

namespace OnionPayload

/-- `true` exactly for a terminal payload. -/
def isFinal : OnionPayload → Bool
  | .final _ => true
  | .forward _ _ => false

theorem isFinal_final (payload : ByteArray) :
    (OnionPayload.final payload).isFinal = true := rfl

theorem isFinal_forward (hop : OnionHop) (next : OnionPacket) :
    (OnionPayload.forward hop next).isFinal = false := rfl

end OnionPayload

/-- Peel the outermost layer.  Peeling is total: an empty layer list yields
the terminal payload, a non-empty one yields the head hop and the inner
packet. -/
def peel (p : OnionPacket) : Option OnionPayload :=
  match p.layers with
  | [] => some (.final p.routingInfo)
  | l :: ls => some (.forward l.hop { p with layers := ls })

theorem peel_nil (version : Nat) (ephemeralKey : PubKey) (routingInfo : ByteArray)
    (hmac : ByteArray) :
    peel ⟨version, ephemeralKey, routingInfo, [], hmac⟩ =
      some (.final routingInfo) := rfl

theorem peel_cons (version : Nat) (ephemeralKey : PubKey) (routingInfo : ByteArray)
    (l : OnionLayer) (ls : List OnionLayer) (hmac : ByteArray) :
    peel ⟨version, ephemeralKey, routingInfo, l :: ls, hmac⟩ =
      some (.forward l.hop ⟨version, ephemeralKey, routingInfo, ls, hmac⟩) := rfl

/-- Peeling never fails. -/
theorem peel_isSome (p : OnionPacket) : (peel p).isSome = true := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => rfl
  | cons l ls => rfl

/-- **Terminal detection.**  `peel` returns a final payload exactly when no
layers remain, and the payload is the packet's `routingInfo`. -/
theorem peel_final_iff (p : OnionPacket) (payload : ByteArray) :
    peel p = some (.final payload) ↔ p.layers = [] ∧ payload = p.routingInfo := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => simp [peel, eq_comm]
  | cons l ls => simp [peel]

/-- One successful peel removes exactly the head layer. -/
theorem peel_forward_layers {p : OnionPacket} {hop : OnionHop}
    {next : OnionPacket} (h : peel p = some (.forward hop next)) :
    next.layers = p.layers.tail := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => simp [peel] at h
  | cons l ls =>
    simp [peel] at h
    rcases h with ⟨_, hnext⟩
    rw [← hnext]
    rfl

/-! ## Opening with an HMAC verifier -/

/-- The abstract onion interface.  `verifyHmac` is the only cryptographic
operation the peel/check step uses.  `hmacBinding` is a *named assumption*
(C8): accepted HMACs are authentic.  It is a `Prop`, never an axiom. -/
structure OnionInterface where
  verifyHmac : ByteArray → ByteArray → Bool
  /-- Assumption C8, stated as a proposition.  Security theorems take this
  as a hypothesis; nothing in this module proves it. -/
  hmacBinding : Prop

/-- Open the outermost layer, accepting it only if the HMAC verifier says
`true`.  Returns `none` for an empty packet or a failed check. -/
def openLayer (I : OnionInterface) (tag : ByteArray) (p : OnionPacket) :
    Option (OnionHop × OnionPacket) :=
  match p.layers with
  | [] => none
  | l :: ls =>
    if I.verifyHmac tag l.hmac then
      some (l.hop, { p with layers := ls })
    else none

theorem openLayer_nil (I : OnionInterface) (tag : ByteArray) (version : Nat)
    (ephemeralKey : PubKey) (routingInfo : ByteArray) (hmac : ByteArray) :
    openLayer I tag ⟨version, ephemeralKey, routingInfo, [], hmac⟩ = none := rfl

/-- **Integrity, mechanical half.**  A successful `openLayer` entails that
the HMAC verifier accepted the head layer.  The cryptographic step from
"verifier accepted" to "the layer is authentic" is assumption C8, named in
`OnionInterface.hmacBinding`, and is not proved. -/
theorem openLayer_verified {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l ∈ p.layers, l.hop = hop ∧ I.verifyHmac tag l.hmac = true := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => simp [openLayer] at h
  | cons l ls =>
    simp only [openLayer] at h
    split at h
    · rename_i hver
      cases h
      exact ⟨l, List.mem_cons_self .., rfl, hver⟩
    · simp at h

/-- A successful open returns the inner packet with the head layer removed. -/
theorem openLayer_next_layers {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    next.layers = p.layers.tail := by
  rcases p with ⟨v, k, r, layers, hm⟩
  cases layers with
  | nil => simp [openLayer] at h
  | cons l ls =>
    simp only [openLayer] at h
    split at h
    · cases h
      rfl
    · simp at h

/-- A failed HMAC check rejects the layer and leaves nothing to peel. -/
theorem openLayer_reject {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {l : OnionLayer} {ls : List OnionLayer}
    (hp : p.layers = l :: ls) (hver : I.verifyHmac tag l.hmac = false) :
    openLayer I tag p = none := by
  rcases p with ⟨v, k, r, layers, hm⟩
  simp only at hp
  subst hp
  simp [openLayer, hver]

/-! ## Peeling all layers -/

/-- Fuel-bounded peel-all, returning the sequence of hops in peel order. -/
def peelAllAux : Nat → OnionPacket → List OnionHop
  | 0, _ => []
  | fuel + 1, p =>
    match p.layers with
    | [] => []
    | l :: ls => l.hop :: peelAllAux fuel { p with layers := ls }

/-- Peel every layer, using the layer count as fuel. -/
def peelAll (p : OnionPacket) : List OnionHop :=
  peelAllAux p.layers.length p

/-- `peelAll` visits every layer and no more. -/
theorem peelAllAux_length (fuel : Nat) :
    ∀ p : OnionPacket, p.layers.length ≤ fuel →
      (peelAllAux fuel p).length = p.layers.length := by
  induction fuel with
  | zero =>
    intro p hp
    rcases p with ⟨v, k, r, layers, hm⟩
    cases layers with
    | nil => simp [peelAllAux]
    | cons l ls => simp at hp
  | succ fuel ih =>
    intro p hp
    rcases p with ⟨v, k, r, layers, hm⟩
    cases layers with
    | nil => simp [peelAllAux]
    | cons l ls =>
      simp only [peelAllAux, List.length_cons]
      have hls : ls.length ≤ fuel := by
        simp only [List.length_cons] at hp
        omega
      rw [ih ⟨v, k, r, ls, hm⟩ hls]

theorem peelAll_length (p : OnionPacket) :
    (peelAll p).length = p.layers.length :=
  peelAllAux_length p.layers.length p (Nat.le_refl _)

/-- **Peel-all layer count equals hop count** for a sealed packet. -/
theorem sealLayers_peelAll_length (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (peelAll (sealLayers version ephemeralKey hops payload)).length = hops.length := by
  rw [peelAll_length]
  simpa [OnionPacket.layerCount] using
    sealLayers_layerCount version ephemeralKey hops payload

/-! ## Structural size bounds -/

/-- Each layer contributes at least one encoded byte. -/
theorem length_le_sum_encoded (ls : List OnionLayer) :
    ls.length ≤ (ls.map OnionLayer.encodedSize).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h : 1 ≤ OnionLayer.encodedSize l := by
      unfold OnionLayer.encodedSize
      omega
    omega

/-- **Layer count is bounded by the encoded size.**  Every layer costs at
least one byte, so a packet cannot hide unboundedly many layers. -/
theorem layerCount_le_encodedSize (p : OnionPacket) :
    p.layers.length ≤ p.encodedSize := by
  have h := length_le_sum_encoded p.layers
  unfold OnionPacket.encodedSize
  omega

/-- The terminal payload plus all sealed layers fit the encoded-size
accounting of the packet. -/
theorem payload_le_encodedSize (p : OnionPacket) :
    p.routingInfo.size ≤ p.encodedSize := by
  unfold OnionPacket.encodedSize
  omega

/-! ## Failure packets (BOLT 4) -/

/-- A BOLT 4 failure message: an error code plus opaque data. -/
structure OnionError where
  code : ErrorCode
  data : ByteArray
deriving Repr

namespace OnionError

/-- Wire size of a padded failure packet:
`2` length bytes + padded failure message (`256`) + `32` HMAC.  Padding is
written as `data + (256 - data)` so the arithmetic exposes the spec's
fixed-size rule. -/
def packetSize (e : OnionError) : Nat :=
  ONION_ERROR_LEN_LEN + e.data.size +
    (ONION_ERROR_PAD - e.data.size) + ONION_ERROR_HMAC_LEN

/-- If the failure data fits the 256-byte padding target, the packet is
exactly 290 bytes.  Larger data would be truncated by the wire encoder,
which this model does not implement. -/
theorem packetSize_eq (e : OnionError) (h : e.data.size ≤ ONION_ERROR_PAD) :
    e.packetSize = ONION_ERROR_PACKET_LEN := by
  unfold packetSize ONION_ERROR_PACKET_LEN
  omega

theorem packetSize_eq_290 (e : OnionError) (h : e.data.size ≤ ONION_ERROR_PAD) :
    e.packetSize = 290 := by
  rw [packetSize_eq e h, onion_error_packet_len_eq]

/-- The empty failure message still encodes a full 290-byte packet. -/
theorem packetSize_empty (code : ErrorCode) :
    (packetSize ⟨code, ByteArray.empty⟩) = 290 := by
  apply packetSize_eq_290
  simp

end OnionError

end LnLean.Routing
