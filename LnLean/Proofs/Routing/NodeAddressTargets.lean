import LnLean.Wire.BigSize
import LnLean.Routing.Gossip

/-!
# LnLean.Proofs.Routing.NodeAddressTargets

Wave-12 parent repair of lane `S12-RT-ADDRESS`, open issue `RT-02`.

This module supplies a faithful, byte-level model of the BOLT 7
`node_announcement` `addresses` field and its typed address descriptors.  The
field is a `u16 addrlen` followed by exactly `addrlen` bytes of concatenated
descriptors:

```text
addresses := addrlen:u16be descriptor*
descriptor :=
  | type 1: [4:ipv4][2:port]                    (6 data bytes, 7 with tag)
  | type 2: [16:ipv6][2:port]                   (18 data bytes, 19 with tag)
  | type 3: [10:torv2][2:port]                  (12 data bytes, 13 with tag)
  | type 4: [35:torv3][2:port]                  (37 data bytes, 38 with tag)
  | type 5: [1:hostname_len][hostname][2:port]  (3 + hostname_len data bytes, up to 258)
```

There is no generic per-descriptor length byte and no `u8` count prefix; the
type-5 `hostname_len` byte is part of that descriptor's payload.  The model
enforces BOLT 7's nonzero port, ASCII hostname, ascending-type order, and
at-most-one type-5 constraints.  It does **not** model DNS resolution, Tor
hostname resolution, peer reachability, `node_announcement` signature
verification, a production gossip store, or P2P framing outside the field.
Punycode is an explicit non-goal; only ASCII hostname bytes are accepted.

No `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`,
`@[implemented_by]`, or `Classical.choice`.
-/

namespace LnLean.Proofs.Routing.NodeAddressTargets

open LnLean
open LnLean.Routing

set_option autoImplicit false

/-! ## 1. Byte and `u16` helpers -/

/-- Consume exactly `n` bytes, returning the payload together with a proof of
its exact length.  The subtype keeps parser proofs out of later rewrites. -/
def takeExact (n : Nat) (l : List UInt8) :
    Option ({ xs : List UInt8 // xs.length = n } × List UInt8) :=
  if h : n ≤ l.length then
    some
      (⟨l.take n, by rw [List.length_take, Nat.min_eq_left h]⟩, l.drop n)
  else none

/-- A successful `takeExact` consumes exactly its requested byte count. -/
theorem takeExact_length {n : Nat} {l : List UInt8}
    {c : { xs : List UInt8 // xs.length = n }} {rest : List UInt8}
    (h : takeExact n l = some (c, rest)) : l.length = n + rest.length := by
  unfold takeExact at h
  split at h
  · rename_i hle
    have h' := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    rw [← h'.2, List.length_drop]
    omega
  · simp at h

/-- A successful `takeExact` leaves at most the original input. -/
theorem takeExact_rest_le {n : Nat} {l : List UInt8}
    {c : { xs : List UInt8 // xs.length = n }} {rest : List UInt8}
    (h : takeExact n l = some (c, rest)) : rest.length ≤ l.length := by
  have := takeExact_length h
  omega

/-- Taking a known payload followed by a suffix recovers that payload. -/
theorem takeExact_append {payload : List UInt8} {n : Nat}
    (h : payload.length = n) (rest : List UInt8) :
    takeExact n (payload ++ rest) = some (⟨payload, h⟩, rest) := by
  subst h
  unfold takeExact
  rw [dif_pos (by simp)]
  simp

/-- `Nat.toUInt8` recovers a small `Nat` through `toNat`. -/
theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) :
    n.toUInt8.toNat = n := by
  rw [show n.toUInt8.toNat = n % 256 from rfl, Nat.mod_eq_of_lt h]

/-- Big-endian `u16` value of two bytes. -/
def u16Value (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- Big-endian `u16` encoding of a small natural number. -/
def u16Bytes (n : Nat) : List UInt8 :=
  [(n / 256).toUInt8, (n % 256).toUInt8]

/-- Decoding the two bytes of `u16Bytes n` recovers `n` when `n < 65536`. -/
theorem u16Value_u16Bytes {n : Nat} (h : n < 65536) :
    u16Value (n / 256).toUInt8 (n % 256).toUInt8 = n := by
  have hdiv : n / 256 < 256 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
    omega
  have hmod : n % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  unfold u16Value
  rw [toUInt8_toNat_of_lt hdiv, toUInt8_toNat_of_lt hmod]
  exact Nat.div_add_mod' n 256

/-! ## 2. Nonzero 16-bit ports -/

/-- A BOLT 7 address port: a `u16` that is explicitly nonzero. -/
structure Port where
  /-- Numeric port value. -/
  val : Nat
  /-- The value fits in 16 bits. -/
  lt_65536 : val < 65536
  /-- BOLT 7 forbids a zero port. -/
  nonzero : val ≠ 0

namespace Port

/-- Big-endian two-byte encoding. -/
def encode (p : Port) : List UInt8 := u16Bytes p.val

/-- Port encodings have length two. -/
theorem encode_length (p : Port) : (encode p).length = 2 := rfl

/-- Port equality is determined by the numeric value. -/
theorem ext {p q : Port} (h : p.val = q.val) : p = q := by
  cases p
  cases q
  simp_all

/-- Parse a big-endian two-byte port, rejecting zero. -/
def parse : List UInt8 → Option (Port × List UInt8)
  | hi :: lo :: rest =>
      if h : u16Value hi lo ≠ 0 then
        some
          (⟨u16Value hi lo,
              by
                have h1 := UInt8.toNat_lt hi
                have h2 := UInt8.toNat_lt lo
                unfold u16Value
                omega,
              h⟩,
            rest)
      else none
  | _ => none

/-- A successful port parse consumes exactly two bytes. -/
theorem parse_length {l : List UInt8} {p : Port} {rest : List UInt8}
    (h : parse l = some (p, rest)) : l.length = 2 + rest.length := by
  cases l with
  | nil => simp [parse] at h
  | cons hi l1 =>
      cases l1 with
      | nil => simp [parse] at h
      | cons lo rest0 =>
          by_cases hv : u16Value hi lo ≠ 0
          · simp only [parse] at h
            rw [dif_pos hv] at h
            have h' := Option.some.inj h
            simp only [Prod.mk.injEq] at h'
            rw [← h'.2]
            simp only [List.length_cons]
            omega
          · simp only [parse] at h
            rw [dif_neg hv] at h
            simp at h

/-- A successful port parse consumes at least one byte. -/
theorem parse_rest_lt {l : List UInt8} {p : Port} {rest : List UInt8}
    (h : parse l = some (p, rest)) : rest.length < l.length := by
  have := parse_length h
  omega

/-- **Port round trip.** -/
theorem parse_encode (p : Port) (rest : List UInt8) :
    parse (encode p ++ rest) = some (p, rest) := by
  have hval : u16Value (p.val / 256).toUInt8 (p.val % 256).toUInt8 = p.val :=
    u16Value_u16Bytes p.lt_65536
  have hne : u16Value (p.val / 256).toUInt8 (p.val % 256).toUInt8 ≠ 0 := by
    rw [hval]
    exact p.nonzero
  simp only [encode, u16Bytes, List.cons_append, List.nil_append, parse]
  rw [dif_pos hne]
  have hp : (⟨u16Value (p.val / 256).toUInt8 (p.val % 256).toUInt8,
      (by
        have h1 := UInt8.toNat_lt (p.val / 256).toUInt8
        have h2 := UInt8.toNat_lt (p.val % 256).toUInt8
        unfold u16Value
        omega),
      hne⟩ : Port) = p := Port.ext hval
  exact congrArg (fun q => some (q, rest)) hp

end Port

/-! ## 3. ASCII hostnames -/

/-- A byte is ASCII when its value is below 128. -/
def isAsciiByte (b : UInt8) : Bool := b.toNat < 128

/-- A hostname is ASCII when every byte is ASCII. -/
def AsciiBytes (l : List UInt8) : Prop := l.all isAsciiByte = true

/-- Executable ASCII test. -/
def asciiBytesB (l : List UInt8) : Bool := l.all isAsciiByte

/-- `AsciiBytes` is decidable. -/
instance (l : List UInt8) : Decidable (AsciiBytes l) := by
  unfold AsciiBytes
  infer_instance

/-- The executable ASCII test is the proposition used by `Address.dns`. -/
theorem asciiBytesB_eq_true_iff (l : List UInt8) :
    asciiBytesB l = true ↔ AsciiBytes l := Iff.rfl

/-! ## 4. Typed address descriptors -/

/-- BOLT 7 address descriptor types. -/
inductive AddressType where
  | ipv4
  | ipv6
  | torV2
  | torV3
  | dns
deriving DecidableEq, Repr

namespace AddressType

/-- The one-byte BOLT 7 tag. -/
def tag : AddressType → UInt8
  | ipv4 => 1
  | ipv6 => 2
  | torV2 => 3
  | torV3 => 4
  | dns => 5

/-- Ascending type rank (equal to the tag value). -/
def rank : AddressType → Nat
  | ipv4 => 1
  | ipv6 => 2
  | torV2 => 3
  | torV3 => 4
  | dns => 5

/-- Decode a tag; zero and unknown tags are rejected. -/
def ofTag (b : UInt8) : Option AddressType :=
  if b = tag .ipv4 then some .ipv4
  else if b = tag .ipv6 then some .ipv6
  else if b = tag .torV2 then some .torV2
  else if b = tag .torV3 then some .torV3
  else if b = tag .dns then some .dns
  else none

theorem ofTag_tag (k : AddressType) : ofTag (tag k) = some k := by
  cases k <;> rfl

theorem tag_injective : Function.Injective tag := by
  intro a b h
  have h' : ofTag (tag a) = ofTag (tag b) := congrArg ofTag h
  rw [ofTag_tag, ofTag_tag] at h'
  exact Option.some.inj h'

theorem tag_ne_zero (k : AddressType) : tag k ≠ 0 := by
  cases k <;> decide

theorem rank_eq_tag_toNat (k : AddressType) : rank k = (tag k).toNat := by
  cases k <;> rfl

theorem rank_pos (k : AddressType) : 0 < rank k := by
  cases k <;> decide

theorem rank_le_five (k : AddressType) : rank k ≤ 5 := by
  cases k <;> decide

end AddressType

/-- A canonically typed BOLT 7 address descriptor.  Fixed layouts carry exact
data-width proofs (excluding the type tag and port); the DNS constructor
carries a `u8`-representable, ASCII hostname.  Every constructor carries a
nonzero `Port`. -/
inductive Address where
  | ipv4 (addr : List UInt8) (port : Port) (h : addr.length = 4)
  | ipv6 (addr : List UInt8) (port : Port) (h : addr.length = 16)
  | torV2 (onion : List UInt8) (port : Port) (h : onion.length = 10)
  | torV3 (onion : List UInt8) (port : Port) (h : onion.length = 35)
  | dns (host : List UInt8) (port : Port) (h : host.length < 256)
      (hascii : AsciiBytes host)

namespace Address

/-- Descriptor type. -/
def kind : Address → AddressType
  | ipv4 .. => .ipv4
  | ipv6 .. => .ipv6
  | torV2 .. => .torV2
  | torV3 .. => .torV3
  | dns .. => .dns

/-- Descriptor port. -/
def port : Address → Port
  | ipv4 _ p _ => p
  | ipv6 _ p _ => p
  | torV2 _ p _ => p
  | torV3 _ p _ => p
  | dns _ p _ _ => p

/-- Descriptor data, excluding the type tag.  There is no per-descriptor
length byte except the explicit `hostname_len` byte in type 5. -/
def data : Address → List UInt8
  | ipv4 addr port _ => addr ++ Port.encode port
  | ipv6 addr port _ => addr ++ Port.encode port
  | torV2 onion port _ => onion ++ Port.encode port
  | torV3 onion port _ => onion ++ Port.encode port
  | dns host port _ _ => host.length.toUInt8 :: (host ++ Port.encode port)

/-- Canonical descriptor encoding: one tag followed by the type-specific data. -/
def encode (a : Address) : List UInt8 := a.kind.tag :: a.data

/-- Parse one type-specific payload after the tag has been consumed. -/
def parsePayload : AddressType → List UInt8 → Option (Address × List UInt8)
  | .ipv4, rest =>
      match takeExact 4 rest with
      | none => none
      | some (addr, rest1) =>
          match Port.parse rest1 with
          | none => none
          | some (port, rest2) => some (ipv4 addr.val port addr.property, rest2)
  | .ipv6, rest =>
      match takeExact 16 rest with
      | none => none
      | some (addr, rest1) =>
          match Port.parse rest1 with
          | none => none
          | some (port, rest2) => some (ipv6 addr.val port addr.property, rest2)
  | .torV2, rest =>
      match takeExact 10 rest with
      | none => none
      | some (onion, rest1) =>
          match Port.parse rest1 with
          | none => none
          | some (port, rest2) => some (torV2 onion.val port onion.property, rest2)
  | .torV3, rest =>
      match takeExact 35 rest with
      | none => none
      | some (onion, rest1) =>
          match Port.parse rest1 with
          | none => none
          | some (port, rest2) => some (torV3 onion.val port onion.property, rest2)
  | .dns, rest =>
      match rest with
      | [] => none
      | lenByte :: rest1 =>
          match takeExact lenByte.toNat rest1 with
          | none => none
          | some (host, rest2) =>
              match Port.parse rest2 with
              | none => none
              | some (port, rest3) =>
                  if hascii : asciiBytesB host.val = true then
                    some
                      (dns host.val port
                        (by
                          have hs := host.property
                          have hlt := UInt8.toNat_lt lenByte
                          omega)
                        ((asciiBytesB_eq_true_iff host.val).1 hascii),
                        rest3)
                  else none

/-- Parse one descriptor from the front of a byte list. -/
def parse : List UInt8 → Option (Address × List UInt8)
  | [] => none
  | t :: rest =>
      match AddressType.ofTag t with
      | none => none
      | some k => parsePayload k rest

/-- Decode exactly one descriptor, rejecting trailing bytes. -/
def decode (l : List UInt8) : Option Address :=
  match parse l with
  | some (a, []) => some a
  | _ => none

/-- A successful type-specific parse consumes fewer bytes than are available
before the type tag is counted. -/
theorem parsePayload_rest_lt {k : AddressType} {rest : List UInt8}
    {a : Address} {rest' : List UInt8}
    (h : parsePayload k rest = some (a, rest')) : rest'.length < rest.length + 1 := by
  cases k with
  | ipv4 =>
      simp only [parsePayload] at h
      split at h
      · simp at h
      · rename_i addr rest1 htake
        split at h
        · simp at h
        · rename_i port rest2 hport
          have h1 := takeExact_length htake
          have h2 := Port.parse_length hport
          have h' := Option.some.inj h
          simp only [Prod.mk.injEq] at h'
          rw [← h'.2]
          omega
  | ipv6 =>
      simp only [parsePayload] at h
      split at h
      · simp at h
      · rename_i addr rest1 htake
        split at h
        · simp at h
        · rename_i port rest2 hport
          have h1 := takeExact_length htake
          have h2 := Port.parse_length hport
          have h' := Option.some.inj h
          simp only [Prod.mk.injEq] at h'
          rw [← h'.2]
          omega
  | torV2 =>
      simp only [parsePayload] at h
      split at h
      · simp at h
      · rename_i onion rest1 htake
        split at h
        · simp at h
        · rename_i port rest2 hport
          have h1 := takeExact_length htake
          have h2 := Port.parse_length hport
          have h' := Option.some.inj h
          simp only [Prod.mk.injEq] at h'
          rw [← h'.2]
          omega
  | torV3 =>
      simp only [parsePayload] at h
      split at h
      · simp at h
      · rename_i onion rest1 htake
        split at h
        · simp at h
        · rename_i port rest2 hport
          have h1 := takeExact_length htake
          have h2 := Port.parse_length hport
          have h' := Option.some.inj h
          simp only [Prod.mk.injEq] at h'
          rw [← h'.2]
          omega
  | dns =>
      simp only [parsePayload] at h
      split at h
      · simp at h
      · rename_i lenByte rest1
        split at h
        · simp at h
        · rename_i host rest2 htake
          split at h
          · simp at h
          · rename_i port rest3 hport
            split at h
            · rename_i hascii
              have h1 := takeExact_length htake
              have h2 := Port.parse_length hport
              have h' := Option.some.inj h
              simp only [Prod.mk.injEq] at h'
              rw [← h'.2]
              simp only [List.length_cons]
              omega
            · simp at h

/-- A successful descriptor parse consumes at least one byte. -/
theorem parse_rest_lt {l : List UInt8} {a : Address} {rest : List UInt8}
    (h : parse l = some (a, rest)) : rest.length < l.length := by
  cases l with
  | nil => simp [parse] at h
  | cons t l1 =>
      simp only [parse] at h
      split at h
      · simp at h
      · rename_i k hk
        have hp := parsePayload_rest_lt h
        simp only [List.length_cons]
        omega

/-- **Descriptor round trip.** -/
theorem parse_encode (a : Address) (rest : List UInt8) :
    parse (encode a ++ rest) = some (a, rest) := by
  cases a with
  | ipv4 addr port hlen =>
      simp only [encode, data, kind, AddressType.tag]
      simp [parse, parsePayload, AddressType.ofTag, AddressType.tag]
      rw [takeExact_append hlen]
      dsimp only
      rw [Port.parse_encode]
  | ipv6 addr port hlen =>
      simp only [encode, data, kind, AddressType.tag]
      simp [parse, parsePayload, AddressType.ofTag, AddressType.tag]
      rw [takeExact_append hlen]
      dsimp only
      rw [Port.parse_encode]
  | torV2 onion port hlen =>
      simp only [encode, data, kind, AddressType.tag]
      simp [parse, parsePayload, AddressType.ofTag, AddressType.tag]
      rw [takeExact_append hlen]
      dsimp only
      rw [Port.parse_encode]
  | torV3 onion port hlen =>
      simp only [encode, data, kind, AddressType.tag]
      simp [parse, parsePayload, AddressType.ofTag, AddressType.tag]
      rw [takeExact_append hlen]
      dsimp only
      rw [Port.parse_encode]
  | dns host port hlen hascii =>
      have hlenByte : host.length.toUInt8.toNat = host.length :=
        toUInt8_toNat_of_lt hlen
      have hhost : host.length = host.length.toUInt8.toNat := by
        rw [hlenByte]
      simp only [encode, data, kind, AddressType.tag]
      simp [parse, parsePayload, AddressType.ofTag, AddressType.tag]
      rw [takeExact_append hhost]
      dsimp only
      rw [Port.parse_encode]
      dsimp only
      rw [dif_pos ((asciiBytesB_eq_true_iff host).2 hascii)]

/-- **Decode/encode round trip for one canonical descriptor.** -/
theorem decode_encode (a : Address) : decode (encode a) = some a := by
  unfold decode
  have h : parse (encode a) = some (a, []) := by
    simpa using parse_encode a []
  rw [h]

/-- **Encoder injectivity for descriptors.** -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  have ha := decode_encode a
  have hb := decode_encode b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

/-- Every descriptor has a nonzero port. -/
theorem port_nonzero (a : Address) : a.port.val ≠ 0 := a.port.nonzero

end Address

/-! ## 5. Descriptor-level rejection -/

/-- An unknown or zero type tag is rejected. -/
theorem parse_unknown_type (t : UInt8) (rest : List UInt8)
    (ht : AddressType.ofTag t = none) :
    Address.parse (t :: rest) = none := by
  simp [Address.parse, ht]

/-- Type 0 is not a BOLT 7 descriptor type. -/
theorem parse_zero_type (rest : List UInt8) :
    Address.parse ((0 : UInt8) :: rest) = none := by
  apply parse_unknown_type
  decide

/-- An IPv4 descriptor whose two port bytes are zero is rejected. -/
theorem parse_zero_port_ipv4 (addr : List UInt8) (hlen : addr.length = 4) :
    Address.parse (AddressType.tag .ipv4 :: addr ++ [(0 : UInt8), 0]) = none := by
  simp [Address.parse, Address.parsePayload, AddressType.ofTag, AddressType.tag]
  rw [takeExact_append hlen]
  simp [Port.parse, u16Value]

/-- A DNS descriptor with a non-ASCII hostname byte is rejected. -/
theorem parse_non_ascii_hostname (hostname : List UInt8)
    (hh : hostname.length < 256) (hnonascii : asciiBytesB hostname = false)
    (portBytes : List UInt8) :
    Address.parse (AddressType.tag .dns :: hostname.length.toUInt8 ::
        (hostname ++ portBytes)) = none := by
  have hlen : hostname.length.toUInt8.toNat = hostname.length :=
    toUInt8_toNat_of_lt hh
  have hhost : hostname.length = hostname.length.toUInt8.toNat := by
    rw [hlen]
  simp [Address.parse, Address.parsePayload, AddressType.ofTag, AddressType.tag]
  rw [takeExact_append hhost]
  cases hp : Port.parse portBytes with
  | none => simp [hp]
  | some p =>
      obtain ⟨port, rest⟩ := p
      simp [hp, hnonascii]

/-- The smallest concrete non-ASCII DNS descriptor is rejected. -/
theorem dns_non_ascii_rejected :
    Address.parse ([5, 1, 0x80, 0, 1] : List UInt8) = none := by
  have h : asciiBytesB ([0x80] : List UInt8) = false := by decide
  exact parse_non_ascii_hostname [0x80] (by decide) h [0, 1]

/-- A type 1 IPv4 descriptor truncated before its port is rejected. -/
theorem ipv4_truncated_rejected :
    Address.parse ([1, 192, 168, 0, 1] : List UInt8) = none := by
  simp [Address.parse, Address.parsePayload, AddressType.ofTag, AddressType.tag,
    takeExact, Port.parse]

/-- A DNS descriptor whose hostname length overstates the remaining bytes is
rejected. -/
theorem dns_truncated_hostname_rejected :
    Address.parse ([5, 5, 101, 120] : List UInt8) = none := by
  simp [Address.parse, Address.parsePayload, AddressType.ofTag, AddressType.tag,
    takeExact]

/-! ## 6. Canonical address lists -/

/-- The concatenated descriptor blob inside the `u16 addrlen` field. -/
def encodeAddressBlob (l : List Address) : List UInt8 :=
  (l.map Address.encode).flatten

/-- The complete BOLT 7 `addresses` field. -/
def encodeAddresses (l : List Address) : List UInt8 :=
  u16Bytes (encodeAddressBlob l).length ++ encodeAddressBlob l

/-- Executable ascending-type test. -/
def sortedAddressTypesB : List Address → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
      (a.kind.rank ≤ b.kind.rank) && sortedAddressTypesB (b :: rest)

/-- Ascending-type predicate. -/
def SortedAddressTypes (l : List Address) : Prop := sortedAddressTypesB l = true

/-- Number of type-5 DNS descriptors. -/
def dnsCount (l : List Address) : Nat :=
  (l.filter (fun a => a.kind == .dns)).length

/-- BOLT 7's "MUST NOT announce more than one type 5 DNS hostname". -/
def AtMostOneDns (l : List Address) : Prop := dnsCount l ≤ 1

/-- The list-level constraints not already carried by each `Address` value. -/
def WellOrderedAddressList (l : List Address) : Prop :=
  SortedAddressTypes l ∧ AtMostOneDns l

/-- `WellOrderedAddressList` is decidable. -/
instance (l : List Address) : Decidable (WellOrderedAddressList l) := by
  unfold WellOrderedAddressList SortedAddressTypes AtMostOneDns
  infer_instance

/-- Canonical address lists also fit the `u16 addrlen` framing. -/
def CanonicalAddressList (l : List Address) : Prop :=
  WellOrderedAddressList l ∧ (encodeAddressBlob l).length < 65536

/-- Parse a complete concatenated descriptor blob to the end. -/
def parseAddressList : List UInt8 → Option (List Address)
  | [] => some []
  | t :: rest =>
      match h : Address.parse (t :: rest) with
      | none => none
      | some (a, rest') =>
          match parseAddressList rest' with
          | none => none
          | some as => some (a :: as)
termination_by l => l.length
decreasing_by
  have := Address.parse_rest_lt h
  omega

/-- **Blob round trip.** -/
theorem parseAddressList_encodeAddressBlob (l : List Address) :
    parseAddressList (encodeAddressBlob l) = some l := by
  induction l with
  | nil =>
      simp only [encodeAddressBlob, List.map_nil, List.flatten_nil]
      rw [parseAddressList.eq_1]
  | cons a as ih =>
      change parseAddressList
        (AddressType.tag (Address.kind a) ::
          (Address.data a ++ encodeAddressBlob as)) =
        some (a :: as)
      rw [parseAddressList.eq_2]
      have hparse :
          Address.parse (AddressType.tag (Address.kind a) ::
              (Address.data a ++ encodeAddressBlob as)) =
            some (a, encodeAddressBlob as) := by
        simpa [Address.encode] using Address.parse_encode a (encodeAddressBlob as)
      rw [hparse]
      dsimp only
      rw [ih]

/-- Parse the `u16 addrlen`-prefixed field.  The prefix must equal the exact
number of remaining bytes; the blob must parse completely and satisfy the
list-level canonicality constraints. -/
def decodeAddresses : List UInt8 → Option (List Address)
  | hi :: lo :: rest =>
      if _hlen : u16Value hi lo = rest.length then
        match parseAddressList rest with
        | none => none
        | some as =>
            if _hcanon : WellOrderedAddressList as then some as else none
      else none
  | _ => none

/-- **List round trip** for canonical lists. -/
theorem decodeAddresses_encodeAddresses (l : List Address)
    (h : CanonicalAddressList l) :
    decodeAddresses (encodeAddresses l) = some l := by
  obtain ⟨⟨hsorted, hdns⟩, hfit⟩ := h
  unfold encodeAddresses
  simp only [u16Bytes, List.cons_append, List.nil_append]
  simp only [decodeAddresses]
  rw [u16Value_u16Bytes hfit]
  rw [dif_pos rfl]
  rw [parseAddressList_encodeAddressBlob]
  dsimp only
  rw [dif_pos ⟨hsorted, hdns⟩]

/-- **Encoder injectivity for canonical lists.** -/
theorem encodeAddresses_injective {l₁ l₂ : List Address}
    (h₁ : CanonicalAddressList l₁) (h₂ : CanonicalAddressList l₂)
    (h : encodeAddresses l₁ = encodeAddresses l₂) : l₁ = l₂ := by
  have hd₁ := decodeAddresses_encodeAddresses l₁ h₁
  have hd₂ := decodeAddresses_encodeAddresses l₂ h₂
  rw [h] at hd₁
  rw [hd₁] at hd₂
  exact Option.some.inj hd₂

/-- A `u16 addrlen` that does not equal the remaining byte count is rejected. -/
theorem decodeAddresses_addrlen_mismatch (hi lo : UInt8) (rest : List UInt8)
    (h : u16Value hi lo ≠ rest.length) :
    decodeAddresses (hi :: lo :: rest) = none := by
  simp only [decodeAddresses]
  rw [dif_neg h]

/-- A list that fails the list-level canonicality constraints is rejected,
provided its blob fits the `u16` framing. -/
theorem decodeAddresses_not_canonical {l : List Address}
    (h : ¬ WellOrderedAddressList l)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none := by
  unfold encodeAddresses
  simp only [u16Bytes, List.cons_append, List.nil_append]
  simp only [decodeAddresses]
  rw [u16Value_u16Bytes hfit]
  rw [dif_pos rfl]
  rw [parseAddressList_encodeAddressBlob]
  dsimp only
  rw [dif_neg h]

/-- A list that is not in ascending type order is rejected, provided its blob
fits the `u16` framing. -/
theorem decodeAddresses_not_sorted {l : List Address}
    (h : sortedAddressTypesB l = false)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none := by
  apply decodeAddresses_not_canonical
  · intro hw
    have hs : SortedAddressTypes l := hw.1
    unfold SortedAddressTypes at hs
    rw [h] at hs
    exact Bool.false_ne_true hs
  · exact hfit

/-- A list with more than one type-5 DNS descriptor is rejected, provided its
blob fits the `u16` framing. -/
theorem decodeAddresses_two_dns {l : List Address}
    (h : 1 < dnsCount l)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none := by
  apply decodeAddresses_not_canonical
  · intro hw
    exact (Nat.not_le_of_gt h) hw.2
  · exact hfit

/-! ## 7. Concrete non-vacuous witnesses -/

/-- Port 80. -/
def port80 : Port := ⟨80, by decide, by decide⟩

/-- A concrete type-1 IPv4 descriptor. -/
def ipv4Witness : Address :=
  Address.ipv4 [192, 168, 0, 1] port80 (by decide)

/-- A concrete type-2 IPv6 descriptor. -/
def ipv6Witness : Address :=
  Address.ipv6 [0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1] port80 (by decide)

/-- A concrete deprecated type-3 Tor v2 descriptor. -/
def torV2Witness : Address :=
  Address.torV2 [0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d]
    port80 (by decide)

/-- A concrete type-4 Tor v3 descriptor. -/
def torV3Witness : Address :=
  Address.torV3 [0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d,
      0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d,
      0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d, 0x2d,
      0x2d, 0x2d, 0x2d, 0x2d, 0x2d] port80 (by decide)

/-- A concrete type-5 DNS descriptor. -/
def dnsWitness : Address :=
  Address.dns [101, 120, 97, 109, 112, 108, 101] port80 (by decide) (by decide)

theorem ipv4Witness_roundtrip :
    Address.decode (Address.encode ipv4Witness) = some ipv4Witness :=
  Address.decode_encode ipv4Witness

theorem ipv6Witness_roundtrip :
    Address.decode (Address.encode ipv6Witness) = some ipv6Witness :=
  Address.decode_encode ipv6Witness

theorem torV2Witness_roundtrip :
    Address.decode (Address.encode torV2Witness) = some torV2Witness :=
  Address.decode_encode torV2Witness

theorem torV3Witness_roundtrip :
    Address.decode (Address.encode torV3Witness) = some torV3Witness :=
  Address.decode_encode torV3Witness

theorem dnsWitness_roundtrip :
    Address.decode (Address.encode dnsWitness) = some dnsWitness :=
  Address.decode_encode dnsWitness

/-- The five witnesses in ascending type order. -/
def witnessList : List Address :=
  [ipv4Witness, ipv6Witness, torV2Witness, torV3Witness, dnsWitness]

theorem witnessList_wellOrdered : WellOrderedAddressList witnessList := by
  decide

theorem witnessList_fits : (encodeAddressBlob witnessList).length < 65536 := by
  decide

theorem witnessList_roundtrip :
    decodeAddresses (encodeAddresses witnessList) = some witnessList :=
  decodeAddresses_encodeAddresses witnessList
    ⟨witnessList_wellOrdered, witnessList_fits⟩

theorem witnessList_encoding_nonempty : encodeAddresses witnessList ≠ [] := by
  decide

theorem witness_kinds_distinct :
    [ipv4Witness.kind, ipv6Witness.kind, torV2Witness.kind,
      torV3Witness.kind, dnsWitness.kind].Nodup := by
  decide

/-- Two DNS descriptors violate BOLT 7's at-most-one-type-5 rule. -/
theorem two_dns_not_wellOrdered :
    ¬ WellOrderedAddressList [dnsWitness, dnsWitness] := by
  decide

theorem two_dns_rejected :
    decodeAddresses (encodeAddresses [dnsWitness, dnsWitness]) = none := by
  apply decodeAddresses_two_dns
  · decide
  · decide

/-! ## 8. Raw bytes do not determine a well-typed address -/

/-- The raw IPv4 data, without its type tag, has no typed decoding. -/
theorem raw_payload_not_decoded :
    Address.decode [192, 168, 0, 1] = none := by
  have h : AddressType.ofTag (192 : UInt8) = none := by decide
  simp [Address.decode, Address.parse, h]

/-- Some raw byte lists have no typed address decoding. -/
theorem raw_decoder_not_total :
    ¬ ∀ b : List UInt8, ∃ a : Address, Address.decode b = some a := by
  intro hall
  obtain ⟨a, ha⟩ := hall []
  simp [Address.decode, Address.parse] at ha

/-- A raw `NodeAnnouncement` can carry bytes in its `addresses` field that are
not a well-typed address without decoding. -/
theorem raw_node_announcement_address_not_typed :
    ∃ (n : NodeAnnouncement) (b : ByteArray),
      b ∈ n.addresses ∧ Address.decode b.data.toList = none := by
  refine ⟨{ nodeId := ⟨ByteArray.empty⟩
            timestamp := 0
            rgbColor := ByteArray.empty
            alias := ByteArray.empty
            addresses := [[192, 168, 0, 1].toByteArray]
            digest := ByteArray.empty
            signature := ⟨ByteArray.empty⟩ },
    [192, 168, 0, 1].toByteArray, ?_, ?_⟩
  · simp
  · simp [raw_payload_not_decoded]

end LnLean.Proofs.Routing.NodeAddressTargets
