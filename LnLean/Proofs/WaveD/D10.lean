/-
# D10 — A Lightning message frame's declared length matches the payload consumed

**English claim.**  After decryption a BOLT 1 Lightning message is laid out as
`type || length || payload`, where the two-byte big-endian `length` field is
the number of payload bytes.  This module proves that the wave-A decoder
`LnLean.Wire.unframe` is *length-total*:

* on every successful decode, the declared length equals the size of the
  payload the decoder actually consumed;
* the consumed payload is exactly the tail after the four-byte header, with
  no trailing bytes left over;
* re-framing the decoded message reproduces the input byte for byte, so the
  decoder accepts exactly the canonical frames whose payload fits the
  two-byte length field;
* a frame whose declared length disagrees with the bytes that follow it is
  rejected.

**BOLT sections.**  BOLT 1 §Lightning Message Format (`type` / `payload` /
optional `extension`; the abstract frame used by the wave-A model carries the
transport's plaintext two-byte length header between `type` and `payload`);
BOLT 1 §Appendix C Message Extension (a full payload leaves no extension
room, which the model's `MAX_MESSAGE_SIZE` already records).

**rust-lightning anchors (commit fe49009).**
* `lightning/src/ln/peer_handler.rs:331` — the custom-message reader is
  handed the already-delimitated message buffer, i.e. the framing layer has
  consumed exactly the declared payload.
* `lightning/src/ln/wire.rs:259-267` — reads a two-byte type and then the
  payload from the fixed-length buffer.
* `lightning/src/ln/peer_channel_encryptor.rs:518-522` — the transport
  length header is a `u16` and `msg_len > 65535` is rejected; `:36`
  `LN_MAX_MSG_LEN = 65535`.

**Not modelled.**  The Noise encryption of the length header (the model keeps
it plaintext), concrete message bodies, and message dispatch.  The target
name `LnLean.Wire.Message.decode_length` in the catalog is not a declaration
in the current model: the decoder is `unframe` / `unframeList` and the
declared length bytes are read locally here by `declaredLength`.  Nothing is
faked: the claims below are about the actual wave-A decoder.
-/

import LnLean.Crypto.Hash
import LnLean.Crypto.Model
import LnLean.Crypto.Sig
import LnLean.Wire.BigSize
import LnLean.Wire.TLV
import LnLean.Wire.Message

namespace LnLean.Proofs.WaveD.D10

open LnLean LnLean.Wire

set_option autoImplicit false

-- OBLIGATION: LN-WD-D10

/-! ## Reading the declared length -/

/-- The two declared length bytes of an abstract frame, read as a `Nat`.
Returns `none` for inputs too short to contain a length field. -/
def declaredLengthList : List UInt8 → Option Nat
  | _ :: _ :: c :: d :: _ => some (u16Nat c d)
  | _ => none

/-- The declared length field of a byte-array frame. -/
def declaredLength (b : ByteArray) : Option Nat :=
  declaredLengthList (bytesToList b)

/-- The payload bytes left after the four-byte `type || length` header. -/
def payloadTailList : List UInt8 → Option (List UInt8)
  | _ :: _ :: _ :: _ :: rest => some rest
  | _ => none

/-- The payload bytes left after the four-byte header of a byte-array frame. -/
def payloadTail (b : ByteArray) : Option (List UInt8) :=
  payloadTailList (bytesToList b)

/-- A two-byte big-endian field is uniquely determined by its numeric value:
the high byte is the quotient by 256 and the low byte the remainder.  This is
the byte-level content of "the declared length is a single well-defined
`u16`". -/
theorem waveD_d10_u16Nat_eq_iff {hi lo : UInt8} {n : Nat} (h : n < 65536) :
    u16Nat hi lo = n ↔ hi = (n / 256).toUInt8 ∧ lo = (n % 256).toUInt8 := by
  constructor
  · intro hsum
    have hhi : hi.toNat < 256 := UInt8.toNat_lt hi
    have hlo : lo.toNat < 256 := UInt8.toNat_lt lo
    have hd : n / 256 < 256 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      omega
    have h1 : lo.toNat = n % 256 := by
      unfold u16Nat at hsum
      omega
    have h2 : hi.toNat = n / 256 := by
      unfold u16Nat at hsum
      omega
    constructor
    · apply UInt8.toNat_inj.mp
      rw [toUInt8_toNat_of_lt hd]
      exact h2
    · apply UInt8.toNat_inj.mp
      rw [toUInt8_toNat_of_lt (Nat.mod_lt n (by decide))]
      exact h1
  · intro ⟨h1, h2⟩
    subst h1
    subst h2
    unfold u16Nat
    rw [toUInt8_toNat_of_lt (by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      omega)]
    rw [toUInt8_toNat_of_lt (Nat.mod_lt n (by decide))]
    omega

/-! ## Decoder inversion -/

/-- Inversion for the frame decoder: a successful decode exposes the four
header bytes, the payload tail, and the declarative equation that the tail's
length is exactly the numeric value of the declared length field. -/
theorem waveD_d10_unframeList_eq_some_iff (l : List UInt8) (m : WireMessage) :
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

/-- A decoded payload always fits the two-byte length field. -/
theorem waveD_d10_unframeList_payload_lt (l : List UInt8) (m : WireMessage)
    (h : unframeList l = some m) : m.payload.size < 65536 := by
  rcases (waveD_d10_unframeList_eq_some_iff l m).mp h with
    ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
  have hhi : c.toNat < 256 := UInt8.toNat_lt c
  have hlo : d.toNat < 256 := UInt8.toNat_lt d
  rw [List.size_toByteArray]
  unfold u16Nat at hlen
  omega

/-- **Declared length law, list form.**  The declared length equals the number
of payload bytes actually consumed. -/
theorem waveD_d10_unframeList_declared_length (l : List UInt8)
    (m : WireMessage) (h : unframeList l = some m) :
    declaredLengthList l = some m.payload.size := by
  rcases (waveD_d10_unframeList_eq_some_iff l m).mp h with
    ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
  simp [declaredLengthList, hlen]

/-- The payload consumed is exactly the bytes after the four-byte header. -/
theorem waveD_d10_unframeList_payload_tail (l : List UInt8) (m : WireMessage)
    (h : unframeList l = some m) :
    payloadTailList l = some (bytesToList m.payload) := by
  rcases (waveD_d10_unframeList_eq_some_iff l m).mp h with
    ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
  simp [payloadTailList, bytesToList_toByteArray]

/-- A successful decode consumes the whole input: no trailing bytes remain. -/
theorem waveD_d10_unframeList_length (l : List UInt8) (m : WireMessage)
    (h : unframeList l = some m) : l.length = 4 + m.payload.size := by
  rcases (waveD_d10_unframeList_eq_some_iff l m).mp h with
    ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
  simp only [List.length_cons]
  rw [List.size_toByteArray]
  omega

/-! ## Byte-array decoder -/

/-- **Declared length law.**  The length field of any successfully decoded
frame equals the size of the payload actually consumed. -/
theorem waveD_d10_decode_declared_length (b : ByteArray) (m : WireMessage)
    (h : unframe b = some m) :
    declaredLength b = some m.payload.size := by
  unfold unframe declaredLength at *
  exact waveD_d10_unframeList_declared_length _ _ h

/-- The decoded payload is exactly the tail after the header. -/
theorem waveD_d10_decode_payload_tail (b : ByteArray) (m : WireMessage)
    (h : unframe b = some m) :
    payloadTail b = some (bytesToList m.payload) := by
  unfold unframe payloadTail at *
  exact waveD_d10_unframeList_payload_tail _ _ h

/-- **Consumption law.**  A successful decode accounts for every input byte:
the frame is the four-byte header plus the declared payload. -/
theorem waveD_d10_decode_length (b : ByteArray) (m : WireMessage)
    (h : unframe b = some m) : b.size = 4 + m.payload.size := by
  have hl : (bytesToList b).length = 4 + m.payload.size :=
    waveD_d10_unframeList_length _ _ h
  rwa [bytesToList_length] at hl

/-- A decoded payload fits the two-byte length field. -/
theorem waveD_d10_decode_payload_lt (b : ByteArray) (m : WireMessage)
    (h : unframe b = some m) : m.payload.size < 65536 := by
  unfold unframe at h
  exact waveD_d10_unframeList_payload_lt _ _ h

/-! ## Canonical frames -/

/-- Re-encoding a decoded message reproduces the input frame byte for byte. -/
theorem waveD_d10_unframeList_some_frame (l : List UInt8) (m : WireMessage)
    (h : unframeList l = some m) : l = bytesToList (frame m) := by
  rcases (waveD_d10_unframeList_eq_some_iff l m).mp h with
    ⟨a, b, c, d, rest, rfl, hlen, rfl⟩
  have hrest : rest.length < 65536 := by
    have hhi : c.toNat < 256 := UInt8.toNat_lt c
    have hlo : d.toNat < 256 := UInt8.toNat_lt d
    unfold u16Nat at hlen
    omega
  have htype : u16Nat a b < 65536 := by
    have hhi : a.toNat < 256 := UInt8.toNat_lt a
    have hlo : b.toNat < 256 := UInt8.toNat_lt b
    unfold u16Nat
    omega
  have hty : a = (u16Nat a b / 256).toUInt8 ∧
      b = (u16Nat a b % 256).toUInt8 :=
    (waveD_d10_u16Nat_eq_iff htype).mp rfl
  have hlen' : c = (rest.length / 256).toUInt8 ∧
      d = (rest.length % 256).toUInt8 :=
    (waveD_d10_u16Nat_eq_iff hrest).mp hlen.symm
  have htypeNat : (u16FromBytes a b).toNat = u16Nat a b := by
    unfold u16FromBytes
    rw [show (UInt16.ofNat (u16Nat a b)).toNat = u16Nat a b % 65536 from by
      simp]
    exact Nat.mod_eq_of_lt htype
  have hsize : rest.toByteArray.size = rest.length := by simp
  show a :: b :: c :: d :: rest =
    bytesToList (u16BE (u16FromBytes a b).toNat ++
      u16BE rest.toByteArray.size ++ rest.toByteArray)
  rw [htypeNat, hsize]
  rw [bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE _ htype]
  rw [bytesToList_u16BE _ hrest]
  simp only [List.cons_append, List.nil_append]
  rw [bytesToList_toByteArray]
  rw [← hty.1, ← hty.2, ← hlen'.1, ← hlen'.2]

/-- Re-encoding a decoded byte array reproduces the frame. -/
theorem waveD_d10_decode_some_frame (b : ByteArray) (m : WireMessage)
    (h : unframe b = some m) : frame m = b := by
  have hl : bytesToList b = bytesToList (frame m) :=
    waveD_d10_unframeList_some_frame _ _ h
  have hcongr := congrArg List.toByteArray hl
  rw [toByteArray_bytesToList, toByteArray_bytesToList] at hcongr
  exact hcongr.symm

/-- A frame decodes iff it is exactly the canonical frame of a message whose
payload fits the two-byte length field.  This is the exact acceptance
criterion: the declared length cannot disagree with the bytes present. -/
theorem waveD_d10_decode_some_iff (b : ByteArray) (m : WireMessage) :
    unframe b = some m ↔ b = frame m ∧ m.payload.size < 65536 := by
  constructor
  · intro h
    exact ⟨(waveD_d10_decode_some_frame b m h).symm,
      waveD_d10_decode_payload_lt b m h⟩
  · rintro ⟨rfl, hlt⟩
    exact unframe_frame m hlt

/-- The declared length of a canonical frame is its payload size. -/
theorem waveD_d10_declaredLength_frame (m : WireMessage)
    (h : m.payload.size < 65536) :
    declaredLength (frame m) = some m.payload.size :=
  waveD_d10_decode_declared_length _ _ (unframe_frame m h)

/-- A frame whose declared length disagrees with the number of payload bytes
is rejected.  (The declared value is any `u16`, not necessarily the canonical
encoding of `n`.) -/
theorem waveD_d10_decode_wrong_length_none (t : MessageType) (p : ByteArray)
    (n : Nat) (hn : n ≠ p.size) (hlt : n < 65536) :
    unframe (u16BE t.toNat ++ u16BE n ++ p) = none := by
  have ht : t.toNat < 65536 := MessageType.toNat_lt t
  have hsize : (bytesToList p).length = p.size := bytesToList_length p
  have hlen : u16Nat (n / 256).toUInt8 (n % 256).toUInt8 = n :=
    u16Nat_roundtrip n hlt
  unfold unframe
  rw [bytesToList_append, bytesToList_append]
  rw [bytesToList_u16BE t.toNat ht]
  rw [bytesToList_u16BE n hlt]
  simp only [List.cons_append, List.nil_append, unframeList]
  rw [hsize, hlen]
  rw [ite_eq_right (fun h => hn h.symm)]

end LnLean.Proofs.WaveD.D10
