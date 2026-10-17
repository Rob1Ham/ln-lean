import LnLean.Basic.Core
import LnLean.Routing.Onion

/-!
# LnLean.Proofs.Routing.OnionProps

English claims of this module:

* **Layers = hops.**  `sealRoute` seals one layer per route hop, so the
  layer count of the resulting packet equals `route.hops.length`
  (`sealRoute_layerCount`).
* **Peel removes exactly one layer and preserves the payload shape.**  A
  forward peel decreases the layer count by one and leaves the version,
  ephemeral key, terminal `routingInfo`, and outer HMAC untouched
  (`peel_forward_layerCount`, `peel_forward_preserves_shape`).
* **The final payload is reached exactly at the last hop.**  After
  `hops.length` peels a sealed packet has no layers left and `peel` returns
  the terminal payload; after any smaller number of peels at least one
  layer remains (`peelExactly_sealLayers_final`,
  `peelExactly_sealLayers_not_final`, `sealLayers_final_at_last_hop`,
  `sealRoute_peelExactly_final`).
* **The wire packet has the fixed BOLT 4 size.**  `OnionPacket.wireSize` is
  always 1366 bytes; the modelled content also fits the 1300-byte
  `hop_payloads` budget whenever the terminal payload plus the encoded
  layers do (`wireSize_eq_1366`, `encodedSize_le_packet_max`).
* **HMAC verification is conditional on the model's HMAC assumption.**
  The mechanical half is unconditional: a successful `openLayer` entails
  that `verifyHmac` accepted the head layer.  The cryptographic half is the
  named C8 assumption `OnionInterface.hmacBinding` plus the explicit
  verifier-binding hypothesis `VerifierBindsTag`
  (`onion_openLayer_verified`, `onion_openLayer_hmac_eq_tag`,
  `onion_openLayer_authentic`).  Nothing here proves forgery resistance.
* **A failure packet is bounded and its origin is recorded.**  The model's
  `OnionError.packetSize` is 290 bytes when the data fits the 256-byte
  padding target and is in particular at most BOLT 4's 32768-byte return
  packet limit.  BOLT 4's exact layout includes one extra `pad_len` field,
  so the spec-size is 292 bytes; both facts are stated
  (`onion_error_packetSize_290`, `bolt4FailurePacketSize_eq`,
  `bolt4FailurePacketSize_eq_model_add_two`).  `AttributedError` records
  the node that originated a failure, and
  `recordHopError_origin_mem_routeNodes` / `recorded_error_bounded` show
  that the record points at a hop of the route and does not change the
  wire size.

BOLT sections (pinned BOLT clone `1aadb719b4007c4cea0ba6e36b08c4fb53788dee`):

* BOLT 4, "Packet Structure" (`refs/bolts/04-onion-routing.md:138`):
  `version` (1 byte), `public_key` (33 bytes), `hop_payloads` (1300
  bytes), `hmac` (32 bytes); the packet is 1366 bytes.
* BOLT 4, "`payload` format" (`refs/bolts/04-onion-routing.md:189`) and
  "Payload for the Last Node" (`refs/bolts/04-onion-routing.md:691`): a
  hop payload carries `amt_to_forward` and `outgoing_cltv_value`; the last
  node has no next channel.
* BOLT 4, "Onion Decryption" (`refs/bolts/04-onion-routing.md:907`):
  unwrap one layer, verify the HMAC, then forward or deliver.
* BOLT 4, "Returning Errors" / "Erring node"
  (`refs/bolts/04-onion-routing.md:1039`, `:1059`) and its Requirements
  (`:1136`): the return packet is `hmac(32) || failure_len(2) ||
  failuremsg || pad_len(2) || pad`, `failure_len + pad_len` is at least
  and should be 256, and the total is at most 32768 bytes.

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:

* `lightning/src/ln/msgs.rs:2741` — `pub struct OnionPacket` with
  `version`, `public_key`, `hop_data: [u8; 20 * 65]`, `hmac: [u8; 32]`.
* `lightning/src/ln/msgs.rs:2725` — `pub struct OnionErrorPacket`
  (`data: Vec<u8>` plus optional attribution data).
* `lightning/src/ln/onion_utils.rs:755` — `ONION_DATA_LEN = 20 * 65`
  (the 1300-byte `hop_payloads` field).
* `lightning/src/ln/onion_utils.rs:471` — `build_onion_payloads`, which
  builds one payload per route hop.
* `lightning/src/ln/onion_utils.rs:52` — `DEFAULT_MIN_FAILURE_PACKET_LEN =
  256`; `:56` — `FAILURE_PACKET_BASE_LEN = 32 + 2 + 2 + 2`, which exhibits
  the extra `pad_len` field omitted by the Lean model.
* `lightning/src/ln/onion_utils.rs:1019` — `build_failure_packet`.
* `lightning/src/ln/onion_payment.rs:505` — `peel_payment_onion`, the
  inbound peel/forward/deliver split.
* `lightning/src/ln/onion_payment.rs:600` —
  `decode_incoming_update_add_htlc_onion`, including the malformed-onion
  error path.

What is **not** modelled (and is therefore not claimed):

* ChaCha20-Poly1305, HKDF, ECDH, and the Sphinx key schedule.  Ciphertexts
  and HMACs are opaque byte arrays; `sealLayers` uses empty ones.
* HMAC unforgeability, onion privacy, unlinkability, and the fixed-size
  size-hiding property.  The only integrity fact proved is the mechanical
  implication "accepted ⇒ verifier returned `true`", conditional on the
  explicit C8 hypothesis.
* The exact TLV/BigSize encoding of hop payloads and the filler
  computation.
* Truncation of failure data larger than 256 bytes, the `pad_len` field in
  the model's `OnionError.packetSize`, attribution data, and the 32768-byte
  truncation rule for oversized return packets.
* Whether the origin recorded in `AttributedError` is authenticated.  The
  base `OnionError` has no origin field; `AttributedError` is a local
  wrapper introduced here so the bookkeeping claim can be stated.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Route hops as onion hops -/

namespace OnionHop

/-- Interpret a BOLT 4 route hop as the routing information carried by one
onion layer.  The amount is supplied by the caller; this module makes no
claim that it is the correct per-hop fee-adjusted amount. -/
def ofRouteHop (h : Hop) (amountMsat : Msat) : OnionHop :=
  { node := h.node
    shortChannelId := h.shortChannelId
    amountMsat := amountMsat
    cltvDelta := h.cltvDelta }

@[simp] theorem ofRouteHop_node (h : Hop) (a : Msat) :
    (ofRouteHop h a).node = h.node := rfl

@[simp] theorem ofRouteHop_scid (h : Hop) (a : Msat) :
    (ofRouteHop h a).shortChannelId = h.shortChannelId := rfl

@[simp] theorem ofRouteHop_amount (h : Hop) (a : Msat) :
    (ofRouteHop h a).amountMsat = a := rfl

@[simp] theorem ofRouteHop_cltvDelta (h : Hop) (a : Msat) :
    (ofRouteHop h a).cltvDelta = h.cltvDelta := rfl

end OnionHop

/-- Seal one structural onion layer per route hop, outermost first. -/
def sealRoute (version : Nat) (ephemeralKey : PubKey) (r : Route)
    (payload : ByteArray) : OnionPacket :=
  sealLayers version ephemeralKey
    (r.hops.map fun h => OnionHop.ofRouteHop h r.amountMsat) payload

/-- **Layer count equals hop count** for a route-sealed packet. -/
theorem sealRoute_layerCount (version : Nat) (ephemeralKey : PubKey)
    (r : Route) (payload : ByteArray) :
    (sealRoute version ephemeralKey r payload).layerCount = r.hops.length := by
  simp [sealRoute, sealLayers, OnionPacket.layerCount]

/-- The layer list of a route-sealed packet has one entry per hop. -/
theorem sealRoute_layers_length (version : Nat) (ephemeralKey : PubKey)
    (r : Route) (payload : ByteArray) :
    (sealRoute version ephemeralKey r payload).layers.length = r.hops.length := by
  simpa [OnionPacket.layerCount] using
    sealRoute_layerCount version ephemeralKey r payload

/-! ## One peel: layer count and payload shape -/

/-- **Peeling reduces the layer count by exactly one.**  The statement is
written as `next.layerCount + 1 = p.layerCount` to avoid truncated
subtraction. -/
theorem peel_forward_layerCount {p : OnionPacket} {hop : OnionHop}
    {next : OnionPacket} (h : peel p = some (.forward hop next)) :
    next.layerCount + 1 = p.layerCount := by
  rcases p with ⟨v, k, ri, layers, hm⟩
  cases layers with
  | nil => simp [peel] at h
  | cons l ls =>
      change some (OnionPayload.forward l.hop ⟨v, k, ri, ls, hm⟩) =
        some (OnionPayload.forward hop next) at h
      cases h
      simp [OnionPacket.layerCount]

/-- **Peeling preserves the payload shape.**  The version, ephemeral key,
terminal payload, and outer HMAC survive a forward peel unchanged; only the
head layer is removed. -/
theorem peel_forward_preserves_shape {p : OnionPacket} {hop : OnionHop}
    {next : OnionPacket} (h : peel p = some (.forward hop next)) :
    next.version = p.version ∧
      next.ephemeralKey = p.ephemeralKey ∧
      next.routingInfo = p.routingInfo ∧
      next.hmac = p.hmac := by
  rcases p with ⟨v, k, ri, layers, hm⟩
  cases layers with
  | nil => simp [peel] at h
  | cons l ls =>
      change some (OnionPayload.forward l.hop ⟨v, k, ri, ls, hm⟩) =
        some (OnionPayload.forward hop next) at h
      cases h
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- A terminal peel exposes the packet's `routingInfo` and no layers remain. -/
theorem peel_final_payload {p : OnionPacket} {payload : ByteArray}
    (h : peel p = some (.final payload)) :
    p.layers = [] ∧ payload = p.routingInfo :=
  (peel_final_iff p payload).mp h

/-! ## Peeling all hops -/

/-- Peel exactly `n` layers, returning the remaining packet.  Returns
`none` if fewer than `n` layers are present. -/
def peelExactly : Nat → OnionPacket → Option OnionPacket
  | 0, p => some p
  | n + 1, p =>
      match p.layers with
      | [] => none
      | _ :: ls => peelExactly n { p with layers := ls }

@[simp] theorem peelExactly_zero (p : OnionPacket) :
    peelExactly 0 p = some p := rfl

@[simp] theorem peelExactly_succ_cons (n : Nat) (version : Nat)
    (ephemeralKey : PubKey) (routingInfo : ByteArray) (l : OnionLayer)
    (ls : List OnionLayer) (hmac : ByteArray) :
    peelExactly (n + 1) ⟨version, ephemeralKey, routingInfo, l :: ls, hmac⟩ =
      peelExactly n ⟨version, ephemeralKey, routingInfo, ls, hmac⟩ := rfl

@[simp] theorem peelExactly_succ_nil (n : Nat) (version : Nat)
    (ephemeralKey : PubKey) (routingInfo : ByteArray) (hmac : ByteArray) :
    peelExactly (n + 1)
      ⟨version, ephemeralKey, routingInfo, [], hmac⟩ = none := rfl

/-- `peelExactly (n + 1)` is the same as one `peel` followed by
`peelExactly n`, on a non-empty layer list.  This connects the step
function to the model's `peel`. -/
theorem peelExactly_succ_eq_peel (n : Nat) (p : OnionPacket) :
    peelExactly (n + 1) p =
      match peel p with
      | some (.forward _ next) => peelExactly n next
      | _ => none := by
  rcases p with ⟨v, k, ri, layers, hm⟩
  cases layers with
  | nil => rfl
  | cons l ls => rfl

/-- Peeling `n` layers leaves `p.layerCount - n` layers. -/
theorem peelExactly_layerCount (n : Nat) (p q : OnionPacket)
    (h : peelExactly n p = some q) :
    q.layerCount + n = p.layerCount := by
  induction n generalizing p with
  | zero =>
      change some p = some q at h
      simp only [Option.some.injEq] at h
      rw [← h]
      simp
  | succ n ih =>
      rcases p with ⟨v, k, ri, layers, hm⟩
      cases layers with
      | nil =>
          change none = some q at h
          simp at h
      | cons l ls =>
          change peelExactly n ⟨v, k, ri, ls, hm⟩ = some q at h
          have hrec := ih ⟨v, k, ri, ls, hm⟩ h
          simp only [OnionPacket.layerCount, List.length_cons] at hrec ⊢
          omega

/-- With enough layers, `peelExactly` returns a packet. -/
theorem peelExactly_exists (n : Nat) (p : OnionPacket)
    (h : n ≤ p.layers.length) :
    ∃ q, peelExactly n p = some q := by
  induction n generalizing p with
  | zero => exact ⟨p, rfl⟩
  | succ n ih =>
      rcases p with ⟨v, k, ri, layers, hm⟩
      cases layers with
      | nil => simp at h
      | cons l ls =>
          have hls : n ≤ ls.length := by
            simp only [List.length_cons] at h
            omega
          obtain ⟨q, hq⟩ := ih ⟨v, k, ri, ls, hm⟩ hls
          exact ⟨q, by simpa using hq⟩

/-- A sealed packet loses exactly one layer per application of
`peelExactly`. -/
theorem sealLayers_peelExactly_layerCount (version : Nat)
    (ephemeralKey : PubKey) (hops : List OnionHop) (payload : ByteArray)
    {n : Nat} (hn : n ≤ hops.length) :
    ∃ q, peelExactly n (sealLayers version ephemeralKey hops payload) = some q ∧
      q.layerCount = hops.length - n := by
  have hlayers :
      (sealLayers version ephemeralKey hops payload).layers.length =
        hops.length := by
    simp [sealLayers]
  obtain ⟨q, hq⟩ :=
    peelExactly_exists n (sealLayers version ephemeralKey hops payload)
      (by rw [hlayers]; exact hn)
  refine ⟨q, hq, ?_⟩
  have hcount' : q.layers.length + n = hops.length := by
    have hcount := peelExactly_layerCount n
      (sealLayers version ephemeralKey hops payload) q hq
    simpa [OnionPacket.layerCount, hlayers] using hcount
  simp only [OnionPacket.layerCount]
  omega

/-- **The last peel is the final peel.**  Peeling exactly `hops.length`
layers from a sealed packet leaves the terminal payload and no layers. -/
theorem peelExactly_sealLayers_final (version : Nat)
    (ephemeralKey : PubKey) (hops : List OnionHop) (payload : ByteArray) :
    peelExactly hops.length (sealLayers version ephemeralKey hops payload) =
      some { version := version
             ephemeralKey := ephemeralKey
             routingInfo := payload
             layers := []
             hmac := ByteArray.empty } := by
  induction hops with
  | nil => rfl
  | cons h hs ih =>
      change peelExactly (hs.length + 1)
        (sealLayers version ephemeralKey (h :: hs) payload) = _
      simp only [sealLayers, List.map_cons]
      change peelExactly hs.length
        { version := version
          ephemeralKey := ephemeralKey
          routingInfo := payload
          layers := hs.map
            (fun h => (⟨h, ByteArray.empty, ByteArray.empty⟩ : OnionLayer))
          hmac := ByteArray.empty } = _
      simpa [sealLayers] using ih

/-- **No earlier peel is final.**  For every `k < hops.length`, a sealed
packet still has at least one layer after `k` peels. -/
theorem peelExactly_sealLayers_not_final (version : Nat)
    (ephemeralKey : PubKey) (hops : List OnionHop) (payload : ByteArray)
    {k : Nat} (hk : k < hops.length) :
    ∃ q, peelExactly k (sealLayers version ephemeralKey hops payload) = some q ∧
      q.layers ≠ [] := by
  obtain ⟨q, hq, hcount⟩ :=
    sealLayers_peelExactly_layerCount version ephemeralKey hops payload
      (Nat.le_of_lt hk)
  refine ⟨q, hq, ?_⟩
  intro hnil
  have hzero : q.layerCount = 0 := by
    simp [OnionPacket.layerCount, hnil]
  omega

/-- **A final payload is reached exactly at the last hop.**  At
`hops.length` peels the packet is empty and peels to the terminal payload;
at every smaller step at least one layer remains. -/
theorem sealLayers_final_at_last_hop (version : Nat)
    (ephemeralKey : PubKey) (hops : List OnionHop) (payload : ByteArray) :
    (∃ q, peelExactly hops.length
        (sealLayers version ephemeralKey hops payload) = some q ∧
      q.layers = [] ∧ peel q = some (.final payload)) ∧
    (∀ k, k < hops.length →
      ∃ q, peelExactly k
          (sealLayers version ephemeralKey hops payload) = some q ∧
        q.layers ≠ []) := by
  constructor
  · refine ⟨_, peelExactly_sealLayers_final version ephemeralKey hops payload,
      rfl, ?_⟩
    simp [peel]
  · intro k hk
    exact peelExactly_sealLayers_not_final version ephemeralKey hops payload hk

/-- Route-level form of `sealLayers_final_at_last_hop`. -/
theorem sealRoute_peelExactly_final (version : Nat) (ephemeralKey : PubKey)
    (r : Route) (payload : ByteArray) :
    ∃ q, peelExactly r.hops.length
        (sealRoute version ephemeralKey r payload) = some q ∧
      q.layers = [] ∧ peel q = some (.final payload) := by
  simpa [sealRoute] using
    (sealLayers_final_at_last_hop version ephemeralKey
      (r.hops.map fun h => OnionHop.ofRouteHop h r.amountMsat) payload).1

/-! ## Structural size bounds -/

/-- The wire packet has exactly the BOLT 4 size: 1366 bytes. -/
theorem wireSize_eq_1366 (p : OnionPacket) : p.wireSize = 1366 := by
  rw [OnionPacket.wireSize_eq_ONION_PACKET_LEN, onion_packet_len_eq]

/-- The wire packet is bounded by the BOLT 4 maximum (in fact equal to it). -/
theorem wireSize_le_1366 (p : OnionPacket) : p.wireSize ≤ 1366 := by
  rw [wireSize_eq_1366]
  exact Nat.le_refl 1366

/-- A sum of `n` copies of `1` is `n`. -/
theorem sum_map_one {α : Type} (l : List α) :
    (l.map fun _ => (1 : Nat)).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]; omega

/-- Structural encoded size of a sealed packet: the terminal payload plus
one byte per layer plus the version marker. -/
theorem sealLayers_encodedSize (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (sealLayers version ephemeralKey hops payload).encodedSize =
      payload.size + hops.length + 1 := by
  simp only [sealLayers, OnionPacket.encodedSize, List.map_map,
    Function.comp_def, OnionLayer.encodedSize, ByteArray.size_empty,
    Nat.add_zero]
  rw [sum_map_one]

/-- If the terminal payload and the encoded layers fit the BOLT 4
1300-byte `hop_payloads` budget, the model's encoded content fits the
1366-byte packet maximum.  (The version marker is the extra modelled byte;
the 33-byte key and 32-byte HMAC belong to `wireSize`, which is a constant.) -/
theorem encodedSize_le_packet_max (p : OnionPacket)
    (h : p.routingInfo.size + (p.layers.map OnionLayer.encodedSize).sum ≤
      HOP_PAYLOADS_LEN) :
    p.encodedSize ≤ ONION_PACKET_LEN := by
  unfold OnionPacket.encodedSize ONION_PACKET_LEN HOP_PAYLOADS_LEN
    ONION_HMAC_LEN at *
  omega

/-- The sealed skeleton respects the same bound under the hop-payload
budget. -/
theorem sealLayers_encodedSize_le_packet_max (version : Nat)
    (ephemeralKey : PubKey) (hops : List OnionHop) (payload : ByteArray)
    (h : payload.size + hops.length ≤ HOP_PAYLOADS_LEN) :
    (sealLayers version ephemeralKey hops payload).encodedSize ≤
      ONION_PACKET_LEN := by
  rw [sealLayers_encodedSize]
  unfold ONION_PACKET_LEN HOP_PAYLOADS_LEN at *
  omega

/-! ## HMAC verification (conditional on C8) -/

/-- The verification-binding property that assumption C8 (HMAC-SHA256,
`docs/ASSUMPTIONS.md`) would supply: for the expected tag `tag`, the
abstract verifier accepts a layer only when the layer carries exactly that
tag.  This is a **hypothesis**, not a theorem; `OnionInterface.hmacBinding`
is an uninterpreted `Prop` and cannot by itself yield this statement. -/
def VerifierBindsTag (I : OnionInterface) (tag : ByteArray)
    (layers : List OnionLayer) : Prop :=
  ∀ l, l ∈ layers → I.verifyHmac tag l.hmac = true → l.hmac = tag

/-- A layer that is both covered by the C8 assumption and tagged with the
expected tag. -/
def LayerAuthentic (I : OnionInterface) (tag : ByteArray)
    (l : OnionLayer) : Prop :=
  I.hmacBinding ∧ l.hmac = tag

/-- Mechanical half of onion integrity: a successful `openLayer` entails
that the verifier accepted the head layer. -/
theorem onion_openLayer_verified {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧ I.verifyHmac tag l.hmac = true :=
  openLayer_verified h

/-- Conditional half: under the verifier-binding condition, a successful
open yields the expected tag on the head layer. -/
theorem onion_openLayer_hmac_eq_tag {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (hbind : VerifierBindsTag I tag p.layers)
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧ l.hmac = tag ∧
      I.verifyHmac tag l.hmac = true := by
  obtain ⟨l, hmem, hhop, hver⟩ := onion_openLayer_verified h
  exact ⟨l, hmem, hhop, hbind l hmem hver, hver⟩

/-- Under C8 (`I.hmacBinding`) and the verifier-binding condition, a
successful open yields an authentic head layer.  This is the strongest
integrity statement in this module; forgery resistance is not proved. -/
theorem onion_openLayer_authentic {I : OnionInterface} {tag : ByteArray}
    {p : OnionPacket} {hop : OnionHop} {next : OnionPacket}
    (hB : I.hmacBinding) (hbind : VerifierBindsTag I tag p.layers)
    (h : openLayer I tag p = some (hop, next)) :
    ∃ l, l ∈ p.layers ∧ l.hop = hop ∧ LayerAuthentic I tag l := by
  obtain ⟨l, hmem, hhop, htag, _⟩ :=
    onion_openLayer_hmac_eq_tag hbind h
  exact ⟨l, hmem, hhop, hB, htag⟩

/-! ## Failure packets: size bound and recorded origin -/

/-- The model's failure packet is 290 bytes when its data fits the
256-byte padding target. -/
theorem onion_error_packetSize_290 (e : OnionError)
    (h : e.data.size ≤ ONION_ERROR_PAD) :
    e.packetSize = 290 :=
  OnionError.packetSize_eq_290 e h

/-- BOLT 4's exact return-packet layout adds a 2-byte `pad_len` after the
failure message; the spec total with `failure_len + pad_len = 256` is 292
bytes. -/
def bolt4FailurePacketSize (e : OnionError) : Nat :=
  ONION_ERROR_HMAC_LEN + ONION_ERROR_LEN_LEN + e.data.size +
    ONION_ERROR_LEN_LEN + (ONION_ERROR_PAD - e.data.size)

/-- With data fitting the padding target, the BOLT 4 return packet is 292
bytes. -/
theorem bolt4FailurePacketSize_eq (e : OnionError)
    (h : e.data.size ≤ ONION_ERROR_PAD) :
    bolt4FailurePacketSize e = 292 := by
  unfold bolt4FailurePacketSize ONION_ERROR_HMAC_LEN ONION_ERROR_PAD
    ONION_ERROR_LEN_LEN at *
  omega

/-- The model's `packetSize` omits the BOLT 4 `pad_len` field: it is
exactly two bytes smaller than the spec layout. -/
theorem bolt4FailurePacketSize_eq_model_add_two (e : OnionError)
    (_h : e.data.size ≤ ONION_ERROR_PAD) :
    bolt4FailurePacketSize e = e.packetSize + 2 := by
  unfold bolt4FailurePacketSize OnionError.packetSize
    ONION_ERROR_HMAC_LEN ONION_ERROR_PAD ONION_ERROR_LEN_LEN at *
  omega

/-- The model's failure packet is within BOLT 4's 32768-byte return limit. -/
theorem onion_error_packetSize_le_32768 (e : OnionError)
    (h : e.data.size ≤ ONION_ERROR_PAD) :
    e.packetSize ≤ 32768 := by
  rw [onion_error_packetSize_290 e h]
  decide

/-- The spec-sized failure packet is also within the 32768-byte limit. -/
theorem bolt4FailurePacketSize_le_32768 (e : OnionError)
    (h : e.data.size ≤ ONION_ERROR_PAD) :
    bolt4FailurePacketSize e ≤ 32768 := by
  rw [bolt4FailurePacketSize_eq e h]
  decide

/-- A failure packet together with the node that originated it.  The base
`OnionError` has no origin field, so this wrapper is where the bookkeeping
claim lives. -/
structure AttributedError where
  origin : NodeId
  error : OnionError
deriving Repr

/-- Record `origin` as the node that produced the failure. -/
def recordError (origin : NodeId) (e : OnionError) : AttributedError :=
  ⟨origin, e⟩

/-- Record a failure produced by a route hop. -/
def recordHopError (h : Hop) (e : OnionError) : AttributedError :=
  recordError h.node e

@[simp] theorem recordError_origin (origin : NodeId) (e : OnionError) :
    (recordError origin e).origin = origin := rfl

@[simp] theorem recordHopError_origin (h : Hop) (e : OnionError) :
    (recordHopError h e).origin = h.node := rfl

/-- Recording an origin does not change the failure packet's wire size. -/
theorem recordError_packetSize (origin : NodeId) (e : OnionError) :
    (recordError origin e).error.packetSize = e.packetSize := rfl

/-- The nodes visited by a route, in hop order. -/
def routeNodes (r : Route) : List NodeId :=
  r.hops.map Hop.node

/-- **The recorded origin is a hop of the route.** -/
theorem recordHopError_origin_mem_routeNodes {r : Route} {h : Hop}
    {e : OnionError} (hh : h ∈ r.hops) :
    (recordHopError h e).origin ∈ routeNodes r := by
  simp only [recordHopError, recordError, routeNodes, List.mem_map]
  exact ⟨h, hh, rfl⟩

/-- **An error packet's size is bounded and its origin hop is recorded.**
The origin is the originating hop's node (a member of the route's node
list), and the model's packet size is 290 bytes while the exact BOLT 4
layout is 292. -/
theorem recorded_error_bounded {r : Route} {h : Hop} {e : OnionError}
    (hh : h ∈ r.hops) (hd : e.data.size ≤ ONION_ERROR_PAD) :
    (recordHopError h e).origin ∈ routeNodes r ∧
      (recordHopError h e).error.packetSize = 290 ∧
      bolt4FailurePacketSize e = 292 := by
  refine ⟨recordHopError_origin_mem_routeNodes hh, ?_, ?_⟩
  · exact onion_error_packetSize_290 e hd
  · exact bolt4FailurePacketSize_eq e hd

end LnLean.Routing
