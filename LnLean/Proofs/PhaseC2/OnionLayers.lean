import LnLean.Proofs.Routing.OnionProps

/-!
# LnLean.Proofs.PhaseC2.OnionLayers

Structural layer laws for the BOLT 4 Sphinx onion model in
`LnLean.Routing.Onion`.

## English claim

1. **Sealing preserves the layer count.**  `sealLayers` creates exactly one
   layer per hop, so its layer count is the length of the hop list
   (`sealLayers_layerCount_preserved`, `sealLayers_layers_length`).
2. **A non-empty sealed packet can be peeled.**  Peeling a packet built from
   `hop :: hops` returns `some`; in fact it returns the head hop as a
   `forward` payload and the inner packet obtained by dropping that layer
   (`peel_sealLayers_nonempty`, `peel_sealLayers_some`).
3. **A forward peel removes exactly one layer.**  If `peel p` returns
   `forward hop next`, then `next.layerCount + 1 = p.layerCount`
   (`peel_forward_layerCount_decrease`).  The statement uses addition rather
   than truncated subtraction.
4. **The wire packet has the fixed BOLT 4 size.**  `OnionPacket.wireSize` is
   `1366` for every packet, independently of its contents
   (`wireSize_eq_1366_all`).
5. **No cryptographic hypothesis is needed for `peel`.**  `peel` takes no
   `OnionInterface`: its payload is determined structurally by the layer list
   and `routingInfo`.  The forward branch removes the head layer and keeps the
   terminal payload and outer fields, while the final branch exposes
   `routingInfo` exactly when no layers remain
   (`peel_forward_payload_structural`, `peel_final_payload_structural`).  In
   particular, the C8 HMAC assumption is not smuggled in as an axiom.

BOLT sections:

* BOLT 4, "Packet Structure": `version` (1 byte), `public_key` (33 bytes),
  `hop_payloads` (1300 bytes), `hmac` (32 bytes); the packet is 1366 bytes.
* BOLT 4, "Onion Decryption": unwrap one layer, verify the HMAC, then either
  forward or deliver.
* BOLT 4, "Payload for the Last Node": the terminal payload is reached when no
  further layers remain.

`rust-lightning` anchors at the pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:

* `lightning/src/ln/onion_utils.rs:50` — `OnionPacket` (`version`,
  `public_key`, `hop_payloads`, `hmac`).
* `lightning/src/ln/onion_utils.rs:755` — `ONION_DATA_LEN = 20 * 65`, the
  1300-byte `hop_payloads` field.
* `lightning/src/ln/onion_utils.rs:471` — `build_onion_payloads`, one payload
  per route hop.
* `lightning/src/ln/onion_payment.rs:505` — `peel_payment_onion`, the inbound
  peel / forward / deliver split.

What is explicitly **not** modelled:

* ChaCha20-Poly1305, HKDF, ECDH, and the Sphinx key schedule.  Ciphertexts and
  HMACs are opaque byte arrays.
* HMAC unforgeability (C8).  The structural `peel` does not check a MAC;
  `openLayer` is the checked variant, and its cryptographic half is an explicit
  hypothesis in `LnLean.Proofs.Routing.OnionProps`, not an axiom here.
* The TLV/BigSize encoding of hop payloads, filler computation, and the exact
  contents of the 1300-byte `hop_payloads` field.
* Onion privacy, unlinkability, and size hiding.
-/

namespace LnLean.Routing

set_option autoImplicit false

/-! ## Sealing preserves the layer count -/

/-- **Layer count equals hop count** for `sealLayers`: sealing preserves the
number of layers, one per hop. -/
theorem sealLayers_layerCount_preserved (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (sealLayers version ephemeralKey hops payload).layerCount = hops.length := by
  simp [sealLayers, OnionPacket.layerCount]

/-- The layer list of a sealed packet has exactly one entry per hop. -/
theorem sealLayers_layers_length (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (sealLayers version ephemeralKey hops payload).layers.length = hops.length := by
  simpa [OnionPacket.layerCount] using
    sealLayers_layerCount_preserved version ephemeralKey hops payload

/-! ## Peeling a non-empty sealed packet -/

/-- The inner packet after peeling `hop` from a sealed packet is exactly the
packet sealed from the remaining hops. -/
theorem peel_sealLayers_cons (version : Nat) (ephemeralKey : PubKey)
    (hop : OnionHop) (hops : List OnionHop) (payload : ByteArray) :
    peel (sealLayers version ephemeralKey (hop :: hops) payload) =
      some (.forward hop (sealLayers version ephemeralKey hops payload)) := rfl

/-- **A non-empty sealed packet peels.**  Peeling a packet sealed from
`hop :: hops` returns a `forward` payload carrying `hop` and the inner packet
with the head layer removed. -/
theorem peel_sealLayers_nonempty (version : Nat) (ephemeralKey : PubKey)
    (hop : OnionHop) (hops : List OnionHop) (payload : ByteArray) :
    ∃ next : OnionPacket,
      peel (sealLayers version ephemeralKey (hop :: hops) payload) =
        some (.forward hop next) :=
  ⟨sealLayers version ephemeralKey hops payload,
    peel_sealLayers_cons version ephemeralKey hop hops payload⟩

/-- Peeling any sealed packet returns `some`: a non-empty packet returns a
forward payload, and the empty packet returns the terminal payload. -/
theorem peel_sealLayers_some (version : Nat) (ephemeralKey : PubKey)
    (hops : List OnionHop) (payload : ByteArray) :
    (peel (sealLayers version ephemeralKey hops payload)).isSome = true := by
  cases hops with
  | nil => simp [sealLayers, peel]
  | cons hop hs =>
    obtain ⟨next, hnext⟩ :=
      peel_sealLayers_nonempty version ephemeralKey hop hs payload
    simp [hnext]

/-! ## A forward peel removes exactly one layer -/

/-- **A forward peel decreases the layer count by one.**  Written as
`next.layerCount + 1 = p.layerCount` to avoid truncated subtraction. -/
theorem peel_forward_layerCount_decrease {p : OnionPacket} {hop : OnionHop}
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

/-! ## Fixed wire size -/

/-- **The wire packet is always 1366 bytes.**  `wireSize` ignores the packet
contents, so this is a constant of the BOLT 4 wire format. -/
theorem wireSize_eq_1366_all (p : OnionPacket) : p.wireSize = 1366 := by
  rw [OnionPacket.wireSize_eq_ONION_PACKET_LEN, onion_packet_len_eq]

/-! ## The payload is structural, not cryptographic -/

/-- A forward peel preserves the terminal payload and leaves exactly the tail
of the layer list.  No HMAC verifier or cryptographic hypothesis is involved. -/
theorem peel_forward_payload_structural {p : OnionPacket} {hop : OnionHop}
    {next : OnionPacket} (h : peel p = some (.forward hop next)) :
    next.layers = p.layers.tail ∧ next.routingInfo = p.routingInfo :=
  ⟨peel_forward_layers h, (peel_forward_preserves_shape h).2.2.1⟩

/-- A final peel exposes exactly the packet's terminal `routingInfo` and leaves
no layers.  Again this is structural and requires no cryptographic assumption. -/
theorem peel_final_payload_structural {p : OnionPacket} {payload : ByteArray}
    (h : peel p = some (.final payload)) :
    p.layers = [] ∧ payload = p.routingInfo :=
  peel_final_payload h

end LnLean.Routing
