/-
# BOLT 8 Noise transport interface

**English claim.**  After the `Noise_XK` handshake, each peer holds sending and
receiving keys and nonces.  Transport messages are encrypted with
ChaCha20-Poly1305 using a 12-byte nonce (`4` zero bytes followed by a
little-endian 64-bit counter), and the nonce is incremented after every frame.
Decryption inverts encryption whenever the model's AEAD correctness field
holds; an ideal authenticated channel is represented as an interface with a
round-trip law.

**BOLT sections.**  BOLT 8 §Noise Protocol Instantiation, §Handshake State,
§Encrypting and Sending Messages, §Receiving and Decrypting Messages.

**rust-lightning anchors (commit fe49009).**
* `lightning/src/ln/peer_channel_encryptor.rs:42` — protocol name
  `Noise_XK_secp256k1_ChaChaPoly_SHA256`.
* `lightning/src/ln/peer_channel_encryptor.rs:150-214` — AEAD helpers and the
  12-byte nonce built from a little-endian counter.
* `lightning/src/ln/peer_channel_encryptor.rs:518-552` — encrypting a message
  with a two-byte encrypted length header.
* `lightning/src/ln/peer_channel_encryptor.rs:585-628` — decrypting the length
  header and the message body.

**Not modelled.**  The three-act `Noise_XK` handshake transcript, ephemeral
key generation, ECDH transcript hashing, HKDF chaining-key derivation,
rekeying after 1000 messages, transport padding, and the Poly1305 tag bytes.
The handshake is an interface; only the post-handshake transport is modelled.
-/

import LnLean.Crypto.Model

namespace LnLean.Crypto

set_option autoImplicit false

open LnLean

/-! ## Handshake pattern and session state -/

/-- The only handshake pattern used by BOLT 8. -/
inductive HandshakePattern where
  | XK
deriving Repr, DecidableEq, BEq

/-- Which side of the handshake a state belongs to. -/
inductive NoiseRole where
  | initiator
  | responder
deriving Repr, DecidableEq, BEq

/-- The official BOLT 8 protocol name. -/
def noiseProtocolName : String := "Noise_XK_secp256k1_ChaChaPoly_SHA256"

/-- The post-handshake transport state.  `sendKey`/`recvKey` are the two
directional ChaCha20-Poly1305 keys and the nonce counters start at zero. -/
structure NoiseState where
  pattern : HandshakePattern
  role : NoiseRole
  sendKey : ByteArray
  recvKey : ByteArray
  sendNonce : Nat
  recvNonce : Nat
  handshakeHash : ByteArray
deriving Repr

/-- Little-endian encoding of `n` into exactly `k` bytes. -/
def leBytes (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => (n % 256).toUInt8 :: leBytes (n / 256) k

/-- `leBytes` produces exactly `k` bytes. -/
theorem leBytes_length (n k : Nat) : (leBytes n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

/-- BOLT 8 nonce: 32 zero bits followed by the 64-bit little-endian counter,
for 12 bytes total. -/
def nonceBytes (n : Nat) : ByteArray :=
  ByteArray.mk (List.replicate 4 (0 : UInt8) ++ leBytes n 8).toArray

/-- The nonce is always 12 bytes (BOLT 8 §Encrypting and Sending Messages). -/
theorem nonceBytes_size (n : Nat) : (nonceBytes n).size = 12 := by
  unfold nonceBytes
  change (List.replicate 4 (0 : UInt8) ++ leBytes n 8).length = 12
  simp [leBytes_length]

/-! ## Transport encryption and decryption -/

/-- Encrypt one transport message and advance the send nonce. -/
def transportEncrypt (M : PrimitiveModel) (s : NoiseState) (plaintext : ByteArray) :
    ByteArray × NoiseState :=
  let ciphertext := M.aeadSeal s.sendKey (nonceBytes s.sendNonce) plaintext
  (ciphertext, { s with sendNonce := s.sendNonce + 1 })

/-- Decrypt one transport message.  The receive nonce advances only on a
successful AEAD open, so a forgery does not desynchronise the channel. -/
def transportDecrypt (M : PrimitiveModel) (s : NoiseState) (ciphertext : ByteArray) :
    Option (ByteArray × NoiseState) :=
  match M.aeadOpen s.recvKey (nonceBytes s.recvNonce) ciphertext with
  | some plaintext => some (plaintext, { s with recvNonce := s.recvNonce + 1 })
  | none => none

/-- Encryption advances the send nonce by one. -/
theorem transportEncrypt_sendNonce (M : PrimitiveModel) (s : NoiseState)
    (pt : ByteArray) : (transportEncrypt M s pt).2.sendNonce = s.sendNonce + 1 := rfl

/-- A successful decryption advances the receive nonce by one. -/
theorem transportDecrypt_recvNonce (M : PrimitiveModel) (s : NoiseState)
    (ct : ByteArray) (pt : ByteArray) (s' : NoiseState)
    (h : transportDecrypt M s ct = some (pt, s')) :
    s'.recvNonce = s.recvNonce + 1 := by
  unfold transportDecrypt at h
  split at h
  · cases h
    rfl
  · cases h

/-- **Transport round trip.**  When sender and receiver agree on the key and
nonce (the loopback case), AEAD correctness makes decryption invert
encryption.  This is conditional on the model's `AeadIndCca` field. -/
theorem transportDecrypt_encrypt (M : PrimitiveModel)
    (h : AeadIndCca M.aeadSeal M.aeadOpen) (s : NoiseState) (pt : ByteArray)
    (hk : s.recvKey = s.sendKey) (hn : s.recvNonce = s.sendNonce) :
    transportDecrypt M s (transportEncrypt M s pt).1 =
      some (pt, { s with recvNonce := s.recvNonce + 1 }) := by
  simp [transportEncrypt, transportDecrypt, hk, hn, h.1]

/-- The AEAD ciphertext is exactly the seal output; this is definitional and
records the interface shape used by `Noise` proofs. -/
theorem transportEncrypt_ciphertext (M : PrimitiveModel) (s : NoiseState)
    (pt : ByteArray) :
    (transportEncrypt M s pt).1 = M.aeadSeal s.sendKey (nonceBytes s.sendNonce) pt :=
  rfl

/-! ## Authenticated-channel interface -/

/-- An ideal authenticated channel with a peer identity.  Protocol layers may
assume this interface without knowing the Noise implementation. -/
structure AuthenticatedChannel where
  send : ByteArray → ByteArray
  recv : ByteArray → Option ByteArray
  peer : PubKey
  /-- An honest channel delivers exactly what was sent. -/
  roundtrip : ∀ m : ByteArray, recv (send m) = some m

/-- The interface law, exposed as a theorem for downstream modules. -/
theorem authenticatedChannel_roundtrip (C : AuthenticatedChannel) (m : ByteArray) :
    C.recv (C.send m) = some m :=
  C.roundtrip m

end LnLean.Crypto
