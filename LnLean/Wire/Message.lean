/-
# BOLT 1 message framing

**English claim.**  A Lightning message is a 2-byte big-endian `type` followed
by a payload.  After decryption the transport also carries a 2-byte length
header, so this module models the abstract frame
`type || length || payload`; the length is the payload byte count.  A message
fits iff its type-plus-payload size is at most 65535 bytes.  Types 128–255 are
the commitment-message group, 256–511 the routing group, and 32768–65535
custom types; the optional TLV extension of BOLT 1 Appendix C can only be
appended when the payload does not already fill the maximum.

**BOLT sections.**  BOLT 1 §Lightning Message Format (type/payload layout,
groups, "maximum possible size is 65535 bytes", extension rule);
§Appendix C: Message Extension.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/ln/wire.rs:259-267` — reads a `u16` message type and then
  the payload.
* `lightning/src/ln/wire.rs:450-452` — the `Type::type_id` API is `u16`.
* `lightning/src/ln/peer_channel_encryptor.rs:518-552` — encrypts a two-byte
  length header plus the type-and-payload message, rejecting length > 65535.
* `lightning/src/ln/msgs.rs:3553` — an example typed message
  (`update_add_htlc`).

**Not modelled.**  The concrete body encodings of every message type, the
TLV extension contents, the encrypted transport wrapper (see
`Crypto.Noise`), message dispatch, and the "odd/even unknown type" policy.
The length prefix is modelled as plaintext; on the wire it is part of the
Noise-encrypted header.
-/

import LnLean.Wire.BigSize

namespace LnLean.Wire

set_option autoImplicit false

open LnLean

/-! ## Message types -/

/-- BOLT 1 message types are unsigned 16-bit values. -/
abbrev MessageType := UInt16

namespace MessageType

/-- Build a message type from a `Nat`, truncating modulo `2^16`. -/
def ofNat (n : Nat) : MessageType := n.toUInt16

/-- Commitment-message group (BOLT 1: types `128`–`255`). -/
def isCommitment (t : MessageType) : Prop :=
  128 ≤ t.toNat ∧ t.toNat ≤ 255

/-- Routing-message group (BOLT 1: types `256`–`511`). -/
def isRouting (t : MessageType) : Prop :=
  256 ≤ t.toNat ∧ t.toNat ≤ 511

/-- Custom-message group (BOLT 1: types `32768`–`65535`). -/
def isCustom (t : MessageType) : Prop :=
  32768 ≤ t.toNat ∧ t.toNat ≤ 65535

/-- A message type always fits in 16 bits. -/
theorem toNat_lt (t : MessageType) : t.toNat < 65536 := by
  have h := UInt16.toNat_lt t
  omega

end MessageType

/-! ## Frames -/

/-- A wire message: a type and an opaque payload. -/
structure WireMessage where
  type : MessageType
  payload : ByteArray
deriving Repr

/-- Fixed big-endian u16 encoding used by the type and length fields. -/
def u16BE (n : Nat) : ByteArray := beBytes n 2

/-- The BOLT 1 message size: two type bytes plus the payload. -/
def WireMessage.messageSize (m : WireMessage) : Nat := 2 + m.payload.size

/-- Maximum BOLT 1 message size, including the two-byte type. -/
def MAX_MESSAGE_SIZE : Nat := 65535

/-- Maximum payload, leaving room for the two-byte type. -/
def MAX_PAYLOAD_SIZE : Nat := 65533

/-- A message fits the transport limit. -/
def WireMessage.fits (m : WireMessage) : Prop := m.messageSize ≤ MAX_MESSAGE_SIZE

/-- Bytes still available for an optional TLV extension. -/
def WireMessage.extensionCapacity (m : WireMessage) : Nat :=
  MAX_MESSAGE_SIZE - m.messageSize

/-- Abstract decrypted frame: `type || length || payload`. -/
def frame (m : WireMessage) : ByteArray :=
  u16BE m.type.toNat ++ u16BE m.payload.size ++ m.payload

/-- The frame has four bytes of type/length overhead plus the payload. -/
theorem frame_size (m : WireMessage) : (frame m).size = 4 + m.payload.size := by
  simp [frame, u16BE, beBytes_size, ByteArray.size_append]

/-- Frame size in terms of `messageSize`. -/
theorem frame_size_eq (m : WireMessage) : (frame m).size = m.messageSize + 2 := by
  rw [frame_size]
  unfold WireMessage.messageSize
  omega

/-- `fits` is equivalent to the payload being at most 65533 bytes. -/
theorem fits_iff_payload (m : WireMessage) :
    m.fits ↔ m.payload.size ≤ MAX_PAYLOAD_SIZE := by
  unfold WireMessage.fits WireMessage.messageSize MAX_MESSAGE_SIZE MAX_PAYLOAD_SIZE
  omega

/-- A message with room for the type fits iff its payload is at most 65533. -/
theorem fits_payload_iff (m : WireMessage) :
    m.fits ↔ m.payload.size ≤ 65533 := by
  simpa [MAX_PAYLOAD_SIZE] using fits_iff_payload m

/-- The extension capacity is positive exactly when the message is not full. -/
theorem extension_capacity_pos (m : WireMessage)
    (h : m.messageSize < MAX_MESSAGE_SIZE) : 0 < m.extensionCapacity := by
  unfold WireMessage.extensionCapacity
  omega

/-- A full-size message has no room for an extension (BOLT 1: an extension can
only be added when the payload does not already fill the maximum). -/
theorem no_extension_when_full (m : WireMessage)
    (h : m.messageSize = MAX_MESSAGE_SIZE) : m.extensionCapacity = 0 := by
  unfold WireMessage.extensionCapacity
  omega

/-! ## Type-255 / group boundary facts -/

/-- Type `255` is the top of the commitment-message group. -/
theorem type_255_is_commitment :
    (MessageType.ofNat 255).isCommitment := by
  unfold MessageType.isCommitment MessageType.ofNat
  decide

/-- Type `256` is the bottom of the routing-message group, not commitment. -/
theorem type_256_is_routing :
    (MessageType.ofNat 256).isRouting := by
  unfold MessageType.isRouting MessageType.ofNat
  decide

/-- The commitment and routing groups are disjoint at the 255/256 boundary. -/
theorem type_255_not_routing :
    ¬ (MessageType.ofNat 255).isRouting := by
  unfold MessageType.isRouting MessageType.ofNat
  decide

/-- A custom type is not a commitment type. -/
theorem custom_not_commitment (t : MessageType) (h : t.isCustom) :
    ¬ t.isCommitment := by
  unfold MessageType.isCustom MessageType.isCommitment at *
  omega

/-! ## Decoding and the round trip -/

/-- Big-endian two-byte encoding, as an explicit list. -/
theorem bytesToList_u16BE (n : Nat) (h : n < 65536) :
    bytesToList (u16BE n) = [(n / 256).toUInt8, (n % 256).toUInt8] := by
  unfold u16BE
  rw [bytesToList_beBytes]
  have hdiv : n / 256 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
    have hp : 256 * 256 = 65536 := by decide
    omega
  simp [beBytesAux]
  rw [Nat.mod_eq_of_lt hdiv]

/-- Two bytes reconstruct their 16-bit big-endian value. -/
theorem u16_from_bytes (n : Nat) (h : n < 65536) :
    (n / 256).toUInt8.toNat * 256 + (n % 256).toUInt8.toNat = n := by
  have hdiv : n / 256 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
    have hp : 256 * 256 = 65536 := by decide
    omega
  rw [toUInt8_toNat_of_lt hdiv]
  rw [toUInt8_toNat_of_lt (Nat.mod_lt n (by decide))]
  rw [Nat.mul_comm]
  rw [Nat.div_add_mod]

/-- The big-endian numeric value of two bytes. -/
def u16Nat (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- Build a 16-bit value from two big-endian bytes. -/
def u16FromBytes (hi lo : UInt8) : MessageType := UInt16.ofNat (u16Nat hi lo)

/-- The two-byte encoding followed by decoding is the identity. -/
theorem u16Nat_roundtrip (n : Nat) (h : n < 65536) :
    u16Nat (n / 256).toUInt8 (n % 256).toUInt8 = n := by
  unfold u16Nat
  exact u16_from_bytes n h

/-- Two encoded bytes reconstruct the original 16-bit value. -/
theorem u16FromBytes_roundtrip (n : Nat) (h : n < 65536) :
    u16FromBytes (n / 256).toUInt8 (n % 256).toUInt8 = n.toUInt16 := by
  unfold u16FromBytes
  rw [u16Nat_roundtrip n h]

/-- Parse `type || length || payload`.  Trailing bytes after the declared
payload cause a rejection, so the decoder is length-total. -/
def unframeList : List UInt8 → Option WireMessage
  | a :: b :: c :: d :: rest =>
      if rest.length = u16Nat c d then
        some ⟨u16FromBytes a b, rest.toByteArray⟩
      else none
  | _ => none

/-- The byte list of a byte array converts back to the array. -/
theorem toByteArray_bytesToList (b : ByteArray) :
    (bytesToList b).toByteArray = b := by
  apply ByteArray.ext
  rw [bytesToList, List.data_toByteArray, Array.toArray_toList]

/-- Decode an abstract wire frame. -/
def unframe (b : ByteArray) : Option WireMessage :=
  unframeList (bytesToList b)

/-- **Frame/unframe round trip.**  For a payload that fits a two-byte length
field, decoding the abstract frame returns the original message. -/
theorem unframe_frame (m : WireMessage) (h : m.payload.size < 65536) :
    unframe (frame m) = some m := by
  have ht : m.type.toNat < 65536 := MessageType.toNat_lt m.type
  unfold unframe
  rw [frame, bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE m.type.toNat ht]
  rw [bytesToList_u16BE m.payload.size h]
  simp only [List.cons_append, List.nil_append, unframeList]
  rw [bytesToList_length, u16Nat_roundtrip m.payload.size h]
  simp only [ite_true]
  rw [u16FromBytes_roundtrip m.type.toNat ht, toByteArray_bytesToList]
  simp only [UInt16.ofNat_toNat]

/-- A message that satisfies the BOLT 1 size limit round-trips. -/
theorem unframe_frame_of_fits (m : WireMessage) (h : m.fits) :
    unframe (frame m) = some m := by
  apply unframe_frame
  have hp : m.payload.size ≤ 65533 := (fits_payload_iff m).mp h
  omega

/-! ## Declared length (catalog row LN-CR-006)

The two-byte big-endian field between the type and the payload is the number of
payload bytes.  The decoder `unframe` already rejects frames whose declared
length disagrees with the bytes present; the lemmas below record the positive
direction: on every successful decode the declared length is exactly the number
of bytes consumed, those bytes are precisely the tail after the four-byte
`type || length` header, and the whole frame is that header plus the payload. -/

namespace Message

/-- The declared payload length of an abstract frame, read from the two-byte
big-endian length field.  Returns `none` when the input is too short to carry
the four-byte `type || length` header. -/
def declaredLength? (b : ByteArray) : Option Nat :=
  match bytesToList b with
  | _ :: _ :: c :: d :: _ => some (u16Nat c d)
  | _ => none

/-- Inversion for the frame decoder: a successful decode exposes the four
header bytes, the payload tail, and the equation saying that the tail's length
is exactly the numeric value of the declared length field. -/
theorem unframeList_eq_some_iff (l : List UInt8) (m : WireMessage) :
    unframeList l = some m ↔
      ∃ a b c d rest, l = a :: b :: c :: d :: rest ∧
        rest.length = u16Nat c d ∧
        m = ⟨u16FromBytes a b, rest.toByteArray⟩ := by
  constructor
  · intro h
    cases l with
    | nil => simp [unframeList] at h
    | cons a l1 =>
      cases l1 with
      | nil => simp [unframeList] at h
      | cons b l2 =>
        cases l2 with
        | nil => simp [unframeList] at h
        | cons c l3 =>
          cases l3 with
          | nil => simp [unframeList] at h
          | cons d rest =>
            simp only [unframeList] at h
            by_cases hlen : rest.length = u16Nat c d
            · rw [ite_eq_left hlen] at h
              simp only [Option.some.injEq] at h
              exact ⟨a, b, c, d, rest, rfl, hlen, h.symm⟩
            · rw [ite_eq_right hlen] at h
              simp at h
  · rintro ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
    simp [unframeList, hlen]

/-- **Declared length law (LN-CR-006).**  On every successful decode of an
abstract frame `type || length || payload`:

1. the two-byte declared length equals the size of the payload actually
   consumed;
2. the consumed payload is exactly the tail after the four-byte
   `type || length` header;
3. the frame accounts for every input byte: its size is `4 + payload.size`. -/
theorem decode_length (b : ByteArray) (m : WireMessage) (h : unframe b = some m) :
    declaredLength? b = some m.payload.size ∧
      (bytesToList b).drop 4 = bytesToList m.payload ∧
      b.size = 4 + m.payload.size := by
  have hlist : unframeList (bytesToList b) = some m := by
    simpa [unframe] using h
  rcases (unframeList_eq_some_iff _ _).mp hlist with
    ⟨a, bty, c, d, rest, hb, hlen, hm⟩
  subst hm
  have hdrop : (bytesToList b).drop 4 = rest := by
    rw [hb]
    simp
  refine ⟨?_, ?_, ?_⟩
  · unfold declaredLength?
    rw [hb]
    rw [List.size_toByteArray, hlen]
  · rw [hdrop, bytesToList_toByteArray]
  · have hb_size : b.size = (bytesToList b).length := (bytesToList_length b).symm
    rw [hb_size, hb]
    simp only [List.length_cons]
    rw [List.size_toByteArray]
    omega

end Message

end LnLean.Wire
