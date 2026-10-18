import LnLean.Proofs.Common

/-!
# LnLean.Proofs.PhaseC3.OnionError

**English claim of this module.**  This module composes the failure-packet
facts of `LnLean.Routing.Onion` (`ONION_ERROR_PACKET_LEN`, `ONION_ERROR_PAD`,
`ONION_ERROR_HMAC_LEN`, `OnionError.packetSize`) into a byte-level
seal/parse story for BOLT 4 return packets:

* `sealError` builds the model's return packet from a failure `OnionError`:
  a two-byte `failure_len`, the failure data padded to 256 bytes, and a
  32-byte HMAC tag over the preceding bytes.  When the failure data fits the
  256-byte padding target the encoded packet is exactly 290 bytes, matching
  the existing `OnionError.packetSize = 290` theorem
  (`sealError_length`, `sealError_length_290`,
  `sealError_length_eq_packetSize`).
* `parseError` reads the length prefix, checks the HMAC, and returns the
  first `failure_len` bytes of the padded message.  Parsing a packet built by
  `sealError` returns the original failure data (`parseError_sealError`).
* A packet whose tag is not the keyed MAC is rejected
  (`parseError_reject_bad_hmac`, `parseError_reject_of_verify_false`).

The HMAC assumption is **not proved**.  It is the explicit `Prop`-valued
hypothesis `HmacBinding` (assumption C8 in `docs/ASSUMPTIONS.md`), the same
cryptographic bridge named `OnionInterface.hmacBinding` in
`LnLean.Routing.Onion`; every rejection theorem takes it as a parameter.
Verifier *completeness* (`verify key msg (mac key msg) = true`) is a separate
structural field of `ErrorInterface`.  Nothing here claims forgery
resistance, PRF security, or collision resistance.

**BOLT sections** (pinned BOLT clone
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`):

* BOLT 4, "Erring node" (`refs/bolts/04-onion-routing.md:1059`): a return
  packet is `hmac(32) || failure_len(u16) || failuremsg || pad_len(u16) ||
  pad`.
* BOLT 4, "Returning Errors" (`refs/bolts/04-onion-routing.md:1039`): return
  packets are limited to 32768 bytes.
* BOLT 4, Requirements (`refs/bolts/04-onion-routing.md:1136`): the erring
  node MUST make `failure_len + pad_len` at least 256 and SHOULD make it
  exactly 256.
* BOLT 4, "Packet Structure" (`refs/bolts/04-onion-routing.md:138`): the
  fixed-size HMAC field is 32 bytes.

`rust-lightning` anchors at pinned commit
`fe4900930c6bd5786ec4203274d7cf312776a5a6`:

* `lightning/src/ln/onion_utils.rs:52` —
  `DEFAULT_MIN_FAILURE_PACKET_LEN = 256`.
* `lightning/src/ln/onion_utils.rs:56` — `FAILURE_PACKET_BASE_LEN =
  32 + 2 + 2 + 2`, showing the extra `pad_len` field of the exact BOLT 4
  layout.
* `lightning/src/ln/onion_utils.rs:1019` — `build_failure_packet`.
* `lightning/src/ln/msgs.rs:2725` — `OnionErrorPacket { data, ... }`.
* `lightning/src/ln/msgs.rs:2719` — `DecodedOnionErrorPacket`
  (`hmac`, `failuremsg`, `pad`).

**Model scope and correspondence to BOLT 4.**  The byte layout formalised
here is the one already encoded by `OnionError.packetSize`:
`failure_len(2) || padded-failuremsg(256) || hmac(32)`.  The exact BOLT 4
order is `hmac || failure_len || failuremsg || pad_len || pad`; the extra
two-byte `pad_len` and the leading HMAC are not modelled (see
`OnionProps.bolt4FailurePacketSize_eq`: the spec layout is 292 bytes, the
model layout is 290).  `sealError`/`parseError` therefore prove the
*structural* laws of the model packet, not the BOLT 4 field ordering or its
padding-length encoding.  Also not modelled: the two-byte failure *code*
(`OnionError.code`), TLV encoding of `failuremsg`, attribution data, the
ChaCha20/HKDF return-path obfuscation, and the 32768-byte truncation rule.
-/

namespace LnLean.Proofs.PhaseC3

open LnLean LnLean.Routing

set_option autoImplicit false

/-! ## Bytes and small conversions -/

/-- A byte string, used for the concrete wire layout. -/
abbrev Bytes : Type := List UInt8

/-- Interpret a byte list as a `ByteArray`. -/
def ofBytes (b : Bytes) : ByteArray :=
  ByteArray.mk b.toArray

/-- The bytes of a `ByteArray`, as a list.  This deliberately uses the
underlying `Array.toList` (rather than the executable `ByteArray.toList`
loop) so the round-trip lemmas are structural. -/
def toBytes (b : ByteArray) : Bytes :=
  b.data.toList

@[simp] theorem ofBytes_size (b : Bytes) : (ofBytes b).size = b.length := by
  change b.toArray.size = b.length
  simp

@[simp] theorem ofBytes_toBytes (b : ByteArray) : ofBytes (toBytes b) = b := by
  apply ByteArray.ext
  simp only [ofBytes]
  exact Array.toArray_toList

@[simp] theorem toBytes_length (b : ByteArray) : (toBytes b).length = b.size := by
  simp [toBytes]

@[simp] theorem ofBytes_append (a c : Bytes) :
    ofBytes (a ++ c) = ofBytes a ++ ofBytes c := by
  apply ByteArray.ext
  simp [ofBytes]

/-! ## Failure-packet layout -/

/-- The two-byte big-endian `failure_len` prefix. -/
def encodeLength (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Decode the `failure_len` prefix.  A malformed (shorter than two bytes)
packet decodes to `0`; `parseError` still rejects it because the HMAC check
runs first. -/
def decodeLength : Bytes → Nat
  | hi :: lo :: _ => hi.toNat * 256 + lo.toNat
  | _ => 0

@[simp] theorem encodeLength_length (n : Nat) :
    (encodeLength n).length = ONION_ERROR_LEN_LEN := rfl

/-- Pad the failure data up to the 256-byte BOLT 4 target.  When the data is
longer than the target the subtraction is zero, so the function is total and
does not truncate. -/
def padTo (data : Bytes) : Bytes :=
  data ++ List.replicate (ONION_ERROR_PAD - data.length) (0 : UInt8)

theorem padTo_length (data : Bytes) :
    (padTo data).length = data.length + (ONION_ERROR_PAD - data.length) := by
  simp [padTo]

theorem padTo_length_of_le {data : Bytes} (h : data.length ≤ ONION_ERROR_PAD) :
    (padTo data).length = ONION_ERROR_PAD := by
  rw [padTo_length]
  omega

/-- Under the 256-byte target the prefix recovers the encoded length.  The
proof only needs the bound that matters for failure packets. -/
theorem decodeLength_encodeLength_append {n : Nat} (hn : n ≤ ONION_ERROR_PAD)
    (rest : Bytes) :
    decodeLength (encodeLength n ++ rest) = n := by
  unfold decodeLength encodeLength
  simp only [List.cons_append, List.nil_append, UInt8.toNat_ofNat']
  have h256 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h256]
  have hpad : ONION_ERROR_PAD = 256 := rfl
  have hn' : n ≤ 256 := by rw [← hpad]; exact hn
  have h1 : n / 256 % 256 = n / 256 :=
    Nat.mod_eq_of_lt (by omega)
  have h2 : n % 256 % 256 = n % 256 :=
    Nat.mod_eq_of_lt (Nat.mod_lt n (by decide : 0 < 256))
  rw [h1, h2]
  have hdm := Nat.div_add_mod n 256
  omega

theorem decodeLength_encodeLength {n : Nat} (hn : n ≤ ONION_ERROR_PAD) :
    decodeLength (encodeLength n) = n := by
  simpa using decodeLength_encodeLength_append hn []

/-- Total length of the header before the HMAC tag: `failure_len` plus the
padded message. -/
def ERROR_HEADER_LEN : Nat := ONION_ERROR_LEN_LEN + ONION_ERROR_PAD

/-! ## The abstract HMAC interface -/

/-- The crypto bridge used by the seal/parse pair.  `mac` is HMAC-SHA256 and
`verify` its comparison-based verifier.  `mac_length` is a wire-format fact;
`verify_mac` is verifier completeness.  Neither says anything about forgery
resistance.

The binding assumption C8 is **not** a field: it is the separate
`Prop`-valued hypothesis `HmacBinding` below, taken by every security
theorem.  This keeps the assumption visible at each use site, exactly as
`LnLean.Routing.OnionInterface.hmacBinding` does for the forward onion. -/
structure ErrorInterface where
  /-- HMAC-SHA256: keyed tag of a message. -/
  mac : Bytes → Bytes → Bytes
  /-- Comparison-based tag verifier. -/
  verify : Bytes → Bytes → Bytes → Bool
  /-- The tag is 32 bytes (BOLT 4 / BOLT 1 `sha256` field). -/
  mac_length : ∀ key msg, (mac key msg).length = ONION_ERROR_HMAC_LEN
  /-- A correct tag verifies (interface correctness, not unforgeability). -/
  verify_mac : ∀ key msg, verify key msg (mac key msg) = true

/-- **Assumption C8, as an explicit `Prop`.**  Under a fixed key, the
verifier accepts a tag only when the tag is exactly the keyed MAC of the
message.  This is the HMAC-binding (PRF) consequence used for onion
integrity; it is a hypothesis of the rejection theorems in this module and is
never proved here. -/
def HmacBinding (I : ErrorInterface) : Prop :=
  ∀ (key msg tag : Bytes), I.verify key msg tag = true → tag = I.mac key msg

/-! ## Sealing a failure packet -/

/-- Encode an `OnionError` as the model's BOLT 4 return packet:
`failure_len(2) || padTo(data, 256) || hmac(32)`, where the HMAC covers the
header (length prefix plus padded message).  The failure `code` is not part
of the wire encoding in this model. -/
def sealError (I : ErrorInterface) (key : Bytes) (e : OnionError) : Bytes :=
  let msg := padTo (toBytes e.data)
  let header := encodeLength (toBytes e.data).length ++ msg
  header ++ I.mac key header

/-- The encoded packet has the model's BOLT 4 return-packet length, provided
the failure data fits the 256-byte padding target. -/
theorem sealError_length (I : ErrorInterface) (key : Bytes) (e : OnionError)
    (hfit : e.data.size ≤ ONION_ERROR_PAD) :
    (sealError I key e).length = ONION_ERROR_PACKET_LEN := by
  have hd : (toBytes e.data).length ≤ ONION_ERROR_PAD := by
    simpa using hfit
  have hmsg : (padTo (toBytes e.data)).length = ONION_ERROR_PAD :=
    padTo_length_of_le hd
  unfold sealError
  simp only [List.length_append, encodeLength_length, hmsg, I.mac_length]
  rfl

/-- The encoded packet is exactly 290 bytes.  This is the byte-level form of
`OnionError.packetSize_eq_290`. -/
theorem sealError_length_290 (I : ErrorInterface) (key : Bytes) (e : OnionError)
    (hfit : e.data.size ≤ ONION_ERROR_PAD) :
    (sealError I key e).length = 290 := by
  rw [sealError_length I key e hfit, onion_error_packet_len_eq]

/-- Composition with the existing model: the byte-level length equals the
abstract `OnionError.packetSize`. -/
theorem sealError_length_eq_packetSize (I : ErrorInterface) (key : Bytes)
    (e : OnionError) (hfit : e.data.size ≤ ONION_ERROR_PAD) :
    (sealError I key e).length = e.packetSize := by
  rw [sealError_length I key e hfit]
  exact (OnionError.packetSize_eq e hfit).symm

/-- The sealed packet splits into the authenticated header and the tag. -/
theorem sealError_take_header (I : ErrorInterface) (key : Bytes) (e : OnionError)
    (hfit : e.data.size ≤ ONION_ERROR_PAD) :
    (sealError I key e).take ERROR_HEADER_LEN =
      encodeLength (toBytes e.data).length ++ padTo (toBytes e.data) := by
  have hd : (toBytes e.data).length ≤ ONION_ERROR_PAD := by simpa using hfit
  have hlen : (encodeLength (toBytes e.data).length ++
      padTo (toBytes e.data)).length = ERROR_HEADER_LEN := by
    simp [ERROR_HEADER_LEN, encodeLength_length, padTo_length_of_le hd]
  unfold sealError
  rw [← hlen]
  exact List.take_left

/-- The trailing 32 bytes of a sealed packet are the HMAC tag. -/
theorem sealError_drop_tag (I : ErrorInterface) (key : Bytes) (e : OnionError)
    (hfit : e.data.size ≤ ONION_ERROR_PAD) :
    (sealError I key e).drop ERROR_HEADER_LEN =
      I.mac key (encodeLength (toBytes e.data).length ++ padTo (toBytes e.data)) := by
  have hd : (toBytes e.data).length ≤ ONION_ERROR_PAD := by simpa using hfit
  have hlen : (encodeLength (toBytes e.data).length ++
      padTo (toBytes e.data)).length = ERROR_HEADER_LEN := by
    simp [ERROR_HEADER_LEN, encodeLength_length, padTo_length_of_le hd]
  unfold sealError
  rw [← hlen]
  exact List.drop_left

/-! ## Parsing a failure packet -/

/-- Parse the model's return packet.  The parser takes the header (first
`ERROR_HEADER_LEN` bytes) and the tag (the remaining bytes), requires the
abstract verifier to accept, decodes `failure_len`, and returns that many
bytes of the padded message.  Any other shape is rejected with `none`.

`verify` is checked before the length bound, so a malformed short packet is
rejected by the HMAC branch rather than by a length inspection. -/
def parseError (I : ErrorInterface) (key : Bytes) (wire : Bytes) : Option ByteArray :=
  let header := wire.take ERROR_HEADER_LEN
  let tag := wire.drop ERROR_HEADER_LEN
  if I.verify key header tag then
    let n := decodeLength wire
    if n ≤ ONION_ERROR_PAD then
      some (ofBytes ((wire.drop ONION_ERROR_LEN_LEN).take n))
    else none
  else none

/-- A failed verifier check rejects the packet outright. -/
theorem parseError_reject_of_verify_false (I : ErrorInterface) (key : Bytes)
    (wire : Bytes)
    (hver : I.verify key (wire.take ERROR_HEADER_LEN)
      (wire.drop ERROR_HEADER_LEN) = false) :
    parseError I key wire = none := by
  simp [parseError, hver]

/-- **Invalid HMAC is rejected.**  If the trailing tag is not the keyed MAC
of the header, no packet is returned.  The proof is exactly the C8 binding
hypothesis: `verify` could only accept the tag if it were the MAC. -/
theorem parseError_reject_bad_hmac (I : ErrorInterface) (key : Bytes)
    (wire : Bytes) (hbind : HmacBinding I)
    (hbad : wire.drop ERROR_HEADER_LEN ≠
      I.mac key (wire.take ERROR_HEADER_LEN)) :
    parseError I key wire = none := by
  unfold parseError
  dsimp only
  split
  · rename_i hver
    exact absurd
      (hbind key (wire.take ERROR_HEADER_LEN) (wire.drop ERROR_HEADER_LEN) hver)
      hbad
  · rfl

/-- A successful parse entails that the verifier accepted the header/tag
pair, that the decoded length fits the padding target, and that the result is
the corresponding prefix of the message.  This is the soundness half; it is
purely structural and does not use C8. -/
theorem parseError_sound (I : ErrorInterface) (key : Bytes) (wire : Bytes)
    {data : ByteArray} (h : parseError I key wire = some data) :
    I.verify key (wire.take ERROR_HEADER_LEN) (wire.drop ERROR_HEADER_LEN) = true ∧
      decodeLength wire ≤ ONION_ERROR_PAD ∧
      data = ofBytes ((wire.drop ONION_ERROR_LEN_LEN).take (decodeLength wire)) := by
  unfold parseError at h
  dsimp only at h
  split at h
  · rename_i hver
    split at h
    · rename_i hn
      cases h
      exact ⟨hver, hn, rfl⟩
    · simp at h
  · simp at h

/-! ## Round-trip -/

/-- The parser on a canonical packet: given a length `n` that fits the pad and
a message of exactly 256 bytes, the packet
`encodeLength n || message || mac(header)` parses back to the first `n`
message bytes.  This is the structural core of the round-trip; it needs
verifier completeness but not C8. -/
theorem parseError_canonical (I : ErrorInterface) (key : Bytes) (n : Nat)
    (message : Bytes) (hn : n ≤ ONION_ERROR_PAD)
    (hmsg : message.length = ONION_ERROR_PAD) :
    parseError I key
        (encodeLength n ++ message ++ I.mac key (encodeLength n ++ message)) =
      some (ofBytes (message.take n)) := by
  have hpre : (encodeLength n).length = ONION_ERROR_LEN_LEN := encodeLength_length n
  have hheader : (encodeLength n ++ message).length = ERROR_HEADER_LEN := by
    simp [ERROR_HEADER_LEN, hpre, hmsg]
  have htake :
      (encodeLength n ++ message ++ I.mac key (encodeLength n ++ message)).take
          ERROR_HEADER_LEN = encodeLength n ++ message := by
    rw [← hheader]
    exact List.take_left
  have hdrop :
      (encodeLength n ++ message ++ I.mac key (encodeLength n ++ message)).drop
          ERROR_HEADER_LEN = I.mac key (encodeLength n ++ message) := by
    rw [← hheader]
    exact List.drop_left
  have hdec : decodeLength
      (encodeLength n ++ message ++ I.mac key (encodeLength n ++ message)) = n := by
    have h := decodeLength_encodeLength_append hn
      (message ++ I.mac key (encodeLength n ++ message))
    simpa [List.append_assoc] using h
  have hdrop2 :
      (encodeLength n ++ message ++ I.mac key (encodeLength n ++ message)).drop
          ONION_ERROR_LEN_LEN = message ++ I.mac key (encodeLength n ++ message) := by
    rw [List.append_assoc]
    rw [show ONION_ERROR_LEN_LEN = (encodeLength n).length from hpre.symm]
    exact List.drop_left
  have hver : I.verify key (encodeLength n ++ message)
      (I.mac key (encodeLength n ++ message)) = true :=
    I.verify_mac key (encodeLength n ++ message)
  unfold parseError
  dsimp only
  rw [htake, hdrop, hver, hdec, ite_eq_left hn, hdrop2]
  rw [List.take_append]
  rw [Nat.sub_eq_zero_of_le (by rw [hmsg]; exact hn)]
  simp

/-- **Parse-after-seal.**  Parsing a packet produced by `sealError` returns
the original failure data, when the data fits the 256-byte pad, and under C8
the tag carried by that packet is the keyed MAC of its header.  The
round-trip half also uses the interface's verifier completeness; C8 is what
makes the accepted tag *authentic* rather than merely well-formed. -/
theorem parseError_sealError (I : ErrorInterface) (key : Bytes) (e : OnionError)
    (hfit : e.data.size ≤ ONION_ERROR_PAD) (hbind : HmacBinding I) :
    parseError I key (sealError I key e) = some e.data ∧
      (sealError I key e).drop ERROR_HEADER_LEN =
        I.mac key ((sealError I key e).take ERROR_HEADER_LEN) := by
  have hd : (toBytes e.data).length ≤ ONION_ERROR_PAD := by simpa using hfit
  have hmsg : (padTo (toBytes e.data)).length = ONION_ERROR_PAD :=
    padTo_length_of_le hd
  have hcanon := parseError_canonical I key (toBytes e.data).length
    (padTo (toBytes e.data)) hd hmsg
  have htake : (padTo (toBytes e.data)).take (toBytes e.data).length =
      toBytes e.data := List.take_left
  constructor
  · unfold sealError
    rw [hcanon, htake, ofBytes_toBytes]
  · have hver : I.verify key ((sealError I key e).take ERROR_HEADER_LEN)
        ((sealError I key e).drop ERROR_HEADER_LEN) = true := by
      rw [sealError_take_header I key e hfit, sealError_drop_tag I key e hfit]
      exact I.verify_mac key _
    exact hbind key ((sealError I key e).take ERROR_HEADER_LEN)
      ((sealError I key e).drop ERROR_HEADER_LEN) hver

/-- **Authenticity of the accepted tag.**  Under C8, the tag accepted when
parsing a `sealError` packet is exactly the keyed MAC of its header: binding
rules out any other accepted value. -/
theorem parseError_sealError_tag (I : ErrorInterface) (key : Bytes)
    (e : OnionError) (_hfit : e.data.size ≤ ONION_ERROR_PAD) (hbind : HmacBinding I)
    {tag : Bytes}
    (hver : I.verify key
      ((sealError I key e).take ERROR_HEADER_LEN) tag = true) :
    tag = I.mac key ((sealError I key e).take ERROR_HEADER_LEN) :=
  hbind key _ tag hver

end LnLean.Proofs.PhaseC3
