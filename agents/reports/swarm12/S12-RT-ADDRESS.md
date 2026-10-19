# S12-RT-ADDRESS — BOLT 7 `node_announcement.addresses`

**Lane:** `S12-RT-ADDRESS`  
**Issue:** `RT-02` (address parsing slice; recommended catalog row `LN-RT-002`)  
**Module:** `LnLean/Proofs/Routing/NodeAddressTargets.lean`  
**Report:** `agents/reports/swarm12/S12-RT-ADDRESS.md`  
**Status:** corrected module builds successfully with the scoped command below;
it contains no `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`,
`@[implemented_by]`, or `Classical.choice` in code.

---

## 1. Retraction of the earlier layout and the earlier `sorry`

The first draft of this lane was **wrong** about the BOLT 7 wire format. It used
a `u8` descriptor count followed by descriptors carrying a per-descriptor `u8`
length. BOLT 7 does **not** use either construct:

* the field is `[u16:addrlen][addrlen*byte:addresses]`
  (`refs/bolts/07-routing-gossip.md:302-303`);
* descriptors are concatenated directly; the first byte of each descriptor is
  its type and the following bytes depend on that type
  (`refs/bolts/07-routing-gossip.md:309-324`);
* there is no generic per-descriptor length byte.  Type 5 has its own
  `hostname_len` byte inside its data payload, exactly as specified at
  `refs/bolts/07-routing-gossip.md:324`.

The earlier `decodeAddresses_not_sorted` also contained two `sorry`s and was
unprovable as stated: `encodeAddresses` stores the blob length in a `u16`, so a
list whose blob is at least 65536 bytes cannot be round-tripped at all.  The
current theorem has the explicit hypothesis
`hfit : (encodeAddressBlob l).length < 65536`; there is no `sorry`.

The post-freeze note in `agents/reports/swarm12/S12-AUDIT-BARRIERS.md:878-884`
that this module was in progress and still contained `sorry` is therefore a
snapshot of the old draft.  The current module is clean and builds; that audit
file was **not** edited by this lane.

---

## 2. Authoritative BOLT 7 layout used by the model

Citations are to `refs/bolts/07-routing-gossip.md`:

* `293-303`: `node_announcement` fields, including `u16 addrlen` followed by
  exactly `addrlen` bytes of `addresses`;
* `309-324`: first byte is the descriptor type, then the appropriate number of
  bytes for that type;
* `345`: `addrlen` MUST equal the number of bytes in `addresses`;
* `346`: descriptors MUST be in ascending order;
* `347`: zero-typed descriptors SHOULD NOT appear;
* `349`: a descriptor `port` MUST NOT be 0;
* `354`: a Tor v2 onion service SHOULD NOT be announced (deprecated, not
  forbidden by a MUST);
* `355`: MUST NOT announce more than one type-5 DNS hostname;
* `324-326`: type-5 hostname bytes MUST be ASCII; non-ASCII text must use
  Punycode.

BOLT 7's quoted “length” for fixed types is the **data** length, excluding the
one-byte type tag.  The module models both quantities unambiguously:

| BOLT type | BOLT 7 data layout (`refs/bolts/07-routing-gossip.md`) | BOLT data length (excl. tag) | Wire length incl. tag | Model constructor |
|---:|---|---:|---:|---|
| 1 | `[4:ipv4_addr][2:port]` | **6** | **7** | `Address.ipv4` |
| 2 | `[16:ipv6_addr][2:port]` | **18** | **19** | `Address.ipv6` |
| 3 | deprecated; `[10:torv2][2:port]` | **12** (10 data + 2 port) | **13** | `Address.torV2` |
| 4 | `[35:onion_addr][2:port]` | **37** (35 + 2 port) | **38** | `Address.torV3` |
| 5 | `[1:hostname_len][hostname][2:port]` | `3 + hostname_len`, up to **258** | `4 + hostname_len`, up to **259** | `Address.dns` |

For type 5, `hostname_len` is a `u8`, the module requires
`host.length < 256`, and therefore the largest data length is
`1 + 255 + 2 = 258`, matching BOLT 7.  The port is always encoded as two
big-endian bytes and must be nonzero.

---

## 3. Definitions

There are **35 public definitions**, plus **2 public inductive types**, **1
public structure**, and **2 local decidability instances**.  All names below
are relative to the root namespace
`LnLean.Proofs.Routing.NodeAddressTargets`; for example, `Port.encode` is
`LnLean.Proofs.Routing.NodeAddressTargets.Port.encode`.

### 3.1 Byte and `u16` helpers

* `takeExact (n : Nat) (l : List UInt8) : Option ({ xs : List UInt8 // xs.length = n } × List UInt8)`
  — consume exactly `n` bytes and keep the size proof.
* `u16Value (hi lo : UInt8) : Nat` — big-endian two-byte value.
* `u16Bytes (n : Nat) : List UInt8` — big-endian two-byte encoding.

### 3.2 Ports

* `structure Port` — fields `val : Nat`, `lt_65536 : val < 65536`,
  `nonzero : val ≠ 0`.
* `Port.encode (p : Port) : List UInt8`.
* `Port.parse : List UInt8 → Option (Port × List UInt8)` — rejects a zero
  port and any input shorter than two bytes.

### 3.3 ASCII hostnames

* `isAsciiByte (b : UInt8) : Bool` — `b.toNat < 128`.
* `AsciiBytes (l : List UInt8) : Prop` — every byte is ASCII.
* `asciiBytesB (l : List UInt8) : Bool` — executable version, definitionally
  equal to `AsciiBytes`.

### 3.4 Address types

* `inductive AddressType` — constructors `ipv4`, `ipv6`, `torV2`, `torV3`,
  `dns`.
* `AddressType.tag : AddressType → UInt8` — tags 1 through 5.
* `AddressType.rank : AddressType → Nat` — ranks 1 through 5, equal to the
  tag value.
* `AddressType.ofTag : UInt8 → Option AddressType` — rejects 0 and unknown
  tags.

### 3.5 Typed descriptors

* `inductive Address` — constructors:
  * `ipv4 (addr : List UInt8) (port : Port) (h : addr.length = 4)`;
  * `ipv6 (addr : List UInt8) (port : Port) (h : addr.length = 16)`;
  * `torV2 (onion : List UInt8) (port : Port) (h : onion.length = 10)`;
  * `torV3 (onion : List UInt8) (port : Port) (h : onion.length = 35)`;
  * `dns (host : List UInt8) (port : Port) (h : host.length < 256)
    (hascii : AsciiBytes host)`.
* `Address.kind : Address → AddressType`.
* `Address.port : Address → Port`.
* `Address.data : Address → List UInt8` — descriptor payload excluding the
  type tag; type 5 begins with its `hostname_len` byte.
* `Address.encode : Address → List UInt8` — `kind.tag :: data`; no generic
  per-descriptor length byte.
* `Address.parsePayload : AddressType → List UInt8 → Option (Address × List UInt8)`
  — type-directed payload parser.
* `Address.parse : List UInt8 → Option (Address × List UInt8)` — parser for one
  descriptor, rejecting unknown/zero tags, truncation, zero ports, non-ASCII
  hostnames, and oversized/truncated type-5 hostnames.
* `Address.decode : List UInt8 → Option Address` — exactly one descriptor with
  no trailing bytes.

### 3.6 Canonical address lists

* `encodeAddressBlob (l : List Address) : List UInt8` — concatenates
  `Address.encode` for every descriptor.
* `encodeAddresses (l : List Address) : List UInt8` — prepends
  `u16Bytes (encodeAddressBlob l).length`.
* `sortedAddressTypesB : List Address → Bool` — executable non-decreasing rank
  test.
* `SortedAddressTypes (l : List Address) : Prop` — the Boolean test is `true`.
* `dnsCount (l : List Address) : Nat` — number of type-5 descriptors.
* `AtMostOneDns (l : List Address) : Prop` — `dnsCount l ≤ 1`.
* `WellOrderedAddressList (l : List Address) : Prop` — sorted plus at most one
  DNS descriptor.
* `CanonicalAddressList (l : List Address) : Prop` — well ordered and blob
  length `< 65536`, i.e. representable in the `u16 addrlen`.
* `parseAddressList : List UInt8 → Option (List Address)` — parses a complete
  concatenated blob to the end.
* `decodeAddresses : List UInt8 → Option (List Address)` — parses
  `[u16 addrlen][blob]`, requiring the prefix to equal the exact remaining
  byte count and the parsed list to be well ordered.

### 3.7 Concrete witnesses

* `port80 : Port` — value 80.
* `ipv4Witness : Address` — `192.168.0.1:80`.
* `ipv6Witness : Address` — `2001:db8::1:80`.
* `torV2Witness : Address` — ten `0x2d` bytes with port 80.
* `torV3Witness : Address` — thirty-five `0x2d` bytes with port 80.
* `dnsWitness : Address` — ASCII hostname `example`, port 80.
* `witnessList : List Address` — the five witnesses in ascending type order.

---

## 4. Public theorems (52)

The module contains **52 public theorems**.  Their exact fully-qualified names
and statements are listed below in source order.

### `LnLean.Proofs.Routing.NodeAddressTargets.takeExact_length`

```lean
theorem takeExact_length {n : Nat} {l : List UInt8}
    {c : { xs : List UInt8 // xs.length = n }} {rest : List UInt8}
    (h : takeExact n l = some (c, rest)) : l.length = n + rest.length
```

### `LnLean.Proofs.Routing.NodeAddressTargets.takeExact_rest_le`

```lean
theorem takeExact_rest_le {n : Nat} {l : List UInt8}
    {c : { xs : List UInt8 // xs.length = n }} {rest : List UInt8}
    (h : takeExact n l = some (c, rest)) : rest.length ≤ l.length
```

### `LnLean.Proofs.Routing.NodeAddressTargets.takeExact_append`

```lean
theorem takeExact_append {payload : List UInt8} {n : Nat}
    (h : payload.length = n) (rest : List UInt8) :
    takeExact n (payload ++ rest) = some (⟨payload, h⟩, rest)
```

### `LnLean.Proofs.Routing.NodeAddressTargets.toUInt8_toNat_of_lt`

```lean
theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) :
    n.toUInt8.toNat = n
```

### `LnLean.Proofs.Routing.NodeAddressTargets.u16Value_u16Bytes`

```lean
theorem u16Value_u16Bytes {n : Nat} (h : n < 65536) :
    u16Value (n / 256).toUInt8 (n % 256).toUInt8 = n
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Port.encode_length`

```lean
theorem encode_length (p : Port) : (encode p).length = 2
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Port.ext`

```lean
theorem ext {p q : Port} (h : p.val = q.val) : p = q
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Port.parse_length`

```lean
theorem parse_length {l : List UInt8} {p : Port} {rest : List UInt8}
    (h : parse l = some (p, rest)) : l.length = 2 + rest.length
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Port.parse_rest_lt`

```lean
theorem parse_rest_lt {l : List UInt8} {p : Port} {rest : List UInt8}
    (h : parse l = some (p, rest)) : rest.length < l.length
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Port.parse_encode`

```lean
theorem parse_encode (p : Port) (rest : List UInt8) :
    parse (encode p ++ rest) = some (p, rest)
```

### `LnLean.Proofs.Routing.NodeAddressTargets.asciiBytesB_eq_true_iff`

```lean
theorem asciiBytesB_eq_true_iff (l : List UInt8) :
    asciiBytesB l = true ↔ AsciiBytes l
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.ofTag_tag`

```lean
theorem ofTag_tag (k : AddressType) : ofTag (tag k) = some k
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.tag_injective`

```lean
theorem tag_injective : Function.Injective tag
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.tag_ne_zero`

```lean
theorem tag_ne_zero (k : AddressType) : tag k ≠ 0
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.rank_eq_tag_toNat`

```lean
theorem rank_eq_tag_toNat (k : AddressType) : rank k = (tag k).toNat
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.rank_pos`

```lean
theorem rank_pos (k : AddressType) : 0 < rank k
```

### `LnLean.Proofs.Routing.NodeAddressTargets.AddressType.rank_le_five`

```lean
theorem rank_le_five (k : AddressType) : rank k ≤ 5
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.parsePayload_rest_lt`

```lean
theorem parsePayload_rest_lt {k : AddressType} {rest : List UInt8}
    {a : Address} {rest' : List UInt8}
    (h : parsePayload k rest = some (a, rest')) : rest'.length < rest.length + 1
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.parse_rest_lt`

```lean
theorem parse_rest_lt {l : List UInt8} {a : Address} {rest : List UInt8}
    (h : parse l = some (a, rest)) : rest.length < l.length
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.parse_encode`

```lean
theorem parse_encode (a : Address) (rest : List UInt8) :
    parse (encode a ++ rest) = some (a, rest)
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.decode_encode`

```lean
theorem decode_encode (a : Address) : decode (encode a) = some a
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.encode_injective`

```lean
theorem encode_injective : Function.Injective encode
```

### `LnLean.Proofs.Routing.NodeAddressTargets.Address.port_nonzero`

```lean
theorem port_nonzero (a : Address) : a.port.val ≠ 0
```

### `LnLean.Proofs.Routing.NodeAddressTargets.parse_unknown_type`

```lean
theorem parse_unknown_type (t : UInt8) (rest : List UInt8)
    (ht : AddressType.ofTag t = none) :
    Address.parse (t :: rest) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.parse_zero_type`

```lean
theorem parse_zero_type (rest : List UInt8) :
    Address.parse ((0 : UInt8) :: rest) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.parse_zero_port_ipv4`

```lean
theorem parse_zero_port_ipv4 (addr : List UInt8) (hlen : addr.length = 4) :
    Address.parse (AddressType.tag .ipv4 :: addr ++ [(0 : UInt8), 0]) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.parse_non_ascii_hostname`

```lean
theorem parse_non_ascii_hostname (hostname : List UInt8)
    (hh : hostname.length < 256) (hnonascii : asciiBytesB hostname = false)
    (portBytes : List UInt8) :
    Address.parse (AddressType.tag .dns :: hostname.length.toUInt8 ::
        (hostname ++ portBytes)) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.dns_non_ascii_rejected`

```lean
theorem dns_non_ascii_rejected :
    Address.parse ([5, 1, 0x80, 0, 1] : List UInt8) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.ipv4_truncated_rejected`

```lean
theorem ipv4_truncated_rejected :
    Address.parse ([1, 192, 168, 0, 1] : List UInt8) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.dns_truncated_hostname_rejected`

```lean
theorem dns_truncated_hostname_rejected :
    Address.parse ([5, 5, 101, 120] : List UInt8) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.parseAddressList_encodeAddressBlob`

```lean
theorem parseAddressList_encodeAddressBlob (l : List Address) :
    parseAddressList (encodeAddressBlob l) = some l
```

### `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_encodeAddresses`

```lean
theorem decodeAddresses_encodeAddresses (l : List Address)
    (h : CanonicalAddressList l) :
    decodeAddresses (encodeAddresses l) = some l
```

### `LnLean.Proofs.Routing.NodeAddressTargets.encodeAddresses_injective`

```lean
theorem encodeAddresses_injective {l₁ l₂ : List Address}
    (h₁ : CanonicalAddressList l₁) (h₂ : CanonicalAddressList l₂)
    (h : encodeAddresses l₁ = encodeAddresses l₂) : l₁ = l₂
```

### `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_addrlen_mismatch`

```lean
theorem decodeAddresses_addrlen_mismatch (hi lo : UInt8) (rest : List UInt8)
    (h : u16Value hi lo ≠ rest.length) :
    decodeAddresses (hi :: lo :: rest) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_not_canonical`

```lean
theorem decodeAddresses_not_canonical {l : List Address}
    (h : ¬ WellOrderedAddressList l)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_not_sorted`

```lean
theorem decodeAddresses_not_sorted {l : List Address}
    (h : sortedAddressTypesB l = false)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_two_dns`

```lean
theorem decodeAddresses_two_dns {l : List Address}
    (h : 1 < dnsCount l)
    (hfit : (encodeAddressBlob l).length < 65536) :
    decodeAddresses (encodeAddresses l) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.ipv4Witness_roundtrip`

```lean
theorem ipv4Witness_roundtrip :
    Address.decode (Address.encode ipv4Witness) = some ipv4Witness
```

### `LnLean.Proofs.Routing.NodeAddressTargets.ipv6Witness_roundtrip`

```lean
theorem ipv6Witness_roundtrip :
    Address.decode (Address.encode ipv6Witness) = some ipv6Witness
```

### `LnLean.Proofs.Routing.NodeAddressTargets.torV2Witness_roundtrip`

```lean
theorem torV2Witness_roundtrip :
    Address.decode (Address.encode torV2Witness) = some torV2Witness
```

### `LnLean.Proofs.Routing.NodeAddressTargets.torV3Witness_roundtrip`

```lean
theorem torV3Witness_roundtrip :
    Address.decode (Address.encode torV3Witness) = some torV3Witness
```

### `LnLean.Proofs.Routing.NodeAddressTargets.dnsWitness_roundtrip`

```lean
theorem dnsWitness_roundtrip :
    Address.decode (Address.encode dnsWitness) = some dnsWitness
```

### `LnLean.Proofs.Routing.NodeAddressTargets.witnessList_wellOrdered`

```lean
theorem witnessList_wellOrdered : WellOrderedAddressList witnessList
```

### `LnLean.Proofs.Routing.NodeAddressTargets.witnessList_fits`

```lean
theorem witnessList_fits : (encodeAddressBlob witnessList).length < 65536
```

### `LnLean.Proofs.Routing.NodeAddressTargets.witnessList_roundtrip`

```lean
theorem witnessList_roundtrip :
    decodeAddresses (encodeAddresses witnessList) = some witnessList
```

### `LnLean.Proofs.Routing.NodeAddressTargets.witnessList_encoding_nonempty`

```lean
theorem witnessList_encoding_nonempty : encodeAddresses witnessList ≠ []
```

### `LnLean.Proofs.Routing.NodeAddressTargets.witness_kinds_distinct`

```lean
theorem witness_kinds_distinct :
    [ipv4Witness.kind, ipv6Witness.kind, torV2Witness.kind,
      torV3Witness.kind, dnsWitness.kind].Nodup
```

### `LnLean.Proofs.Routing.NodeAddressTargets.two_dns_not_wellOrdered`

```lean
theorem two_dns_not_wellOrdered :
    ¬ WellOrderedAddressList [dnsWitness, dnsWitness]
```

### `LnLean.Proofs.Routing.NodeAddressTargets.two_dns_rejected`

```lean
theorem two_dns_rejected :
    decodeAddresses (encodeAddresses [dnsWitness, dnsWitness]) = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.raw_payload_not_decoded`

```lean
theorem raw_payload_not_decoded :
    Address.decode [192, 168, 0, 1] = none
```

### `LnLean.Proofs.Routing.NodeAddressTargets.raw_decoder_not_total`

```lean
theorem raw_decoder_not_total :
    ¬ ∀ b : List UInt8, ∃ a : Address, Address.decode b = some a
```

### `LnLean.Proofs.Routing.NodeAddressTargets.raw_node_announcement_address_not_typed`

```lean
theorem raw_node_announcement_address_not_typed :
    ∃ (n : NodeAnnouncement) (b : ByteArray),
      b ∈ n.addresses ∧ Address.decode b.data.toList = none
```


---

## 5. Canonicality constraints and assumptions

### 5.1 Enforced by construction or by the parser

* **Exact `addrlen`.** `decodeAddresses` returns `none` unless
  `u16Value hi lo = rest.length`; see `decodeAddresses_addrlen_mismatch`.
* **Exact descriptor widths.** The `Address` constructors carry
  `addr.length = 4`, `addr.length = 16`, `onion.length = 10`,
  `onion.length = 35`, and `host.length < 256`.
* **Nonzero port.** `Port` stores `nonzero : val ≠ 0`, and `Port.parse` rejects
  two zero port bytes.  `parse_zero_port_ipv4` is the general IPv4 rejection
  theorem.
* **ASCII hostname.** The `dns` constructor stores `AsciiBytes host`, and the
  parser checks `asciiBytesB host = true`.  `parse_non_ascii_hostname` is the
  general rejection theorem.
* **No type 0 and no unknown type.** `AddressType.ofTag` rejects both;
  `parse_zero_type` and `parse_unknown_type` expose this.
* **No trailing bytes.** `Address.decode` requires the parse remainder to be
  `[]`.
* **Truncation rejection.** `ipv4_truncated_rejected` and
  `dns_truncated_hostname_rejected` are concrete witnesses; `takeExact`
  returning `none` gives the general mechanism.

### 5.2 Enforced at list level

* **Ascending type order.** `sortedAddressTypesB` checks
  `rank a ≤ rank b` for each adjacent pair.  This is non-decreasing order, so
  multiple descriptors of the same type 1–4 are allowed; type 5 is separately
  capped at one.
* **At most one type 5.** `AtMostOneDns` and `dnsCount` enforce BOLT 7 line
  355.  `decodeAddresses_two_dns` rejects lists with more than one DNS entry.
* **`u16` framing.** `CanonicalAddressList` includes
  `(encodeAddressBlob l).length < 65536`.  The rejection theorems
  `decodeAddresses_not_canonical`, `decodeAddresses_not_sorted`, and
  `decodeAddresses_two_dns` all take this as an explicit `hfit` hypothesis;
  this is necessary because the length prefix is only a `u16`.

### 5.3 Deliberate boundaries

* **Punycode is not modelled.** Only ASCII hostname bytes are accepted.  BOLT
  7 permits non-ASCII names only after Punycode encoding; this module neither
  implements nor validates Punycode.
* **Tor v2 is accepted but deprecated.** BOLT 7 says a node SHOULD NOT announce
  a Tor v2 service, not MUST NOT, so the model parses type 3 descriptors and
  labels them deprecated rather than rejecting them.
* **Receiving-node policy is stricter than BOLT's SHOULD semantics.** BOLT 7
  says a receiver SHOULD ignore the first unknown descriptor and SHOULD ignore
  zero-port descriptors.  This canonical decoder rejects unknown/zero types,
  zero ports, non-ASCII hostnames, non-ascending lists, and multiple DNS
  entries instead of modelling “ignore and continue”.
* **Not modelled:** IPv4/IPv6 routability, DNS resolution, Tor hostname
  resolution, peer reachability, signature verification, features, timestamp,
  `rgb_color`, `alias`, production gossip storage, P2P framing outside the
  `addresses` field, and Punycode.
* **Raw `NodeAnnouncement` compatibility:** the legacy
  `NodeAnnouncement.addresses : List ByteArray` is untouched.  The module
  provides no production view that silently converts arbitrary raw bytes into
  typed descriptors; `raw_node_announcement_address_not_typed` records that raw
  bytes can fail decoding.

---

## 6. Non-vacuity and concrete rejection witnesses

* The five constructors are all inhabited:
  `ipv4Witness`, `ipv6Witness`, `torV2Witness`, `torV3Witness`, and
  `dnsWitness`.
* Each individual descriptor round-trips:
  `ipv4Witness_roundtrip`, `ipv6Witness_roundtrip`,
  `torV2Witness_roundtrip`, `torV3Witness_roundtrip`, and
  `dnsWitness_roundtrip`.
* `witnessList_wellOrdered` proves the five-element list satisfies the
  list-level canonicality constraints; `witnessList_fits` proves its blob is
  below 65536 bytes; `witnessList_roundtrip` proves the complete field
  round-trips; `witnessList_encoding_nonempty` and `witness_kinds_distinct`
  provide non-emptiness and distinct-type evidence.
* `two_dns_not_wellOrdered` and `two_dns_rejected` are concrete negative
  witnesses for the at-most-one-DNS rule.
* `dns_non_ascii_rejected`, `parse_non_ascii_hostname`,
  `ipv4_truncated_rejected`, `dns_truncated_hostname_rejected`,
  `parse_zero_port_ipv4`, and `parse_zero_type` are concrete/general rejection
  witnesses.
* `raw_payload_not_decoded`, `raw_decoder_not_total`, and
  `raw_node_announcement_address_not_typed` show that the typed decoder is not
  total and that raw `NodeAnnouncement.addresses` bytes do not by themselves
  determine a typed address.

The witness data lengths are 4 (IPv4), 16 (IPv6), 10 (Tor v2), 35 (Tor v3),
and 7 (the ASCII hostname `example`), all with port 80.

---

## 7. Scoped build and forbidden-token scan

Build command, run from `/home/ubuntu/ln-lean-repair`:

```sh
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Routing.NodeAddressTargets
```

Result:

```text
Build completed successfully (9 jobs).
```

The only compiler messages are deprecation warnings for `dif_pos`/`dif_neg`
and one unused-variable linter warning for the equation name in
`parseAddressList`; there are no errors.

Forbidden-token scan:

```sh
grep -nE 'sorry|axiom|admit|native_decide|unsafe|implemented_by|Classical\.choice' \
  LnLean/Proofs/Routing/NodeAddressTargets.lean
```

The only matches are the two documentation lines that say those tokens are
forbidden (lines 32-33).  There is no occurrence in code, and there is no
`#check` or other scratch command left in the file.

This lane wrote only:

* `LnLean/Proofs/Routing/NodeAddressTargets.lean`;
* `agents/reports/swarm12/S12-RT-ADDRESS.md`.

No root import, catalog, traceability, axiom-audit, obligations, docs, scripts,
or tests file was edited by this lane.

---

## 8. Recommended `LN-RT-002` catalog targets

Recommendation: **keep `LN-RT-002` as already proved, add this module as
evidence for the address-parsing slice, and do not claim that `RT-02` is
closed.**  `RT-02` still includes rotation identity, signed chain policy,
wire-level membership, and production gossip-pipeline integration.

Suggested primary catalog target:

1. `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_encodeAddresses`
   — end-to-end canonical `node_announcement.addresses` round-trip with exact
   `u16 addrlen`.

Suggested supporting targets:

2. `LnLean.Proofs.Routing.NodeAddressTargets.parseAddressList_encodeAddressBlob`
   — descriptor-blob round-trip without the length prefix.
3. `LnLean.Proofs.Routing.NodeAddressTargets.Address.parse_encode`
   — single-descriptor parser/printer round-trip.
4. `LnLean.Proofs.Routing.NodeAddressTargets.Address.decode_encode`
   — single-descriptor decode/encode round-trip.
5. `LnLean.Proofs.Routing.NodeAddressTargets.Address.encode_injective`
   — descriptor encoding is injective.
6. `LnLean.Proofs.Routing.NodeAddressTargets.encodeAddresses_injective`
   — canonical list encoding is injective.
7. `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_addrlen_mismatch`
   — exact `addrlen` enforcement.
8. `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_not_sorted`
   — ascending-order rejection, with the required `u16` fit hypothesis.
9. `LnLean.Proofs.Routing.NodeAddressTargets.decodeAddresses_two_dns`
   — at-most-one-type-5 rejection, with the required `u16` fit hypothesis.
10. `LnLean.Proofs.Routing.NodeAddressTargets.witnessList_roundtrip`
    — concrete non-vacuity for all five descriptor types.

Suggested catalog wording:

> `LN-RT-002` — proved. Add `LnLean.Proofs.Routing.NodeAddressTargets` as
> evidence for BOLT 7 `node_announcement.addresses`: a `u16 addrlen` followed
> by concatenated typed descriptors (IPv4, IPv6, deprecated Tor v2, Tor v3, and
> ASCII DNS), with exact byte-length framing, nonzero ports, ascending type
> order, at most one type 5, round-trip on canonical lists, and explicit
> rejection of truncated/malformed/non-canonical inputs. Scope note: this is a
> canonical parser model, not a DNS/Tor resolver, Punycode implementation,
> signature verifier, chain-existence policy, or production gossip pipeline;
> `RT-02` remains narrowed rather than closed.

---

## 9. Limitations and integration notes

* The module is self-contained and is **not** imported by `LnLean.lean`.
  Integration requires the parent/integrator to add the root import and the
  `LN-RT-002` catalog rows; this lane was not allowed to edit shared files.
* The legacy wire record still stores `addresses : List ByteArray`.  This
  module models the field as `List UInt8`; conversion from a `ByteArray` is
  `.data.toList`.  No production view or admission function is added.
* `decodeAddresses_not_sorted` and the other rejection theorems require
  `hfit : (encodeAddressBlob l).length < 65536`.  This is a real precondition,
  not a proof artifact: without it the `u16` length prefix cannot represent the
  blob and round-trip rejection would be false.
* The parser is intentionally strict/canonical.  It does not model BOLT 7's
  receiving-node “ignore the first unknown descriptor” policy, nor the
  SHOULD-level Tor v2 deprecation as a hard rejection.
* No DNS resolution, Tor resolution, routability check, signature check,
  feature/timestamp handling, or gossip-store integration is claimed.
