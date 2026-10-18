import LnLean.Proofs.Channel.SighashTargets

/-!
# H11 — HTLC-wire serialization: round-trip, wire-domain bounds, negatives

**Issues.** `PR-05`, `PR-02`.

`LnLean/Proofs/Channel/SighashTargets.lean` defines `HtlcWire`, its single-output
wire transaction `HtlcWire.toTx`, the serializer `HtlcWire.txBytes`, the
`HtlcWire.WellFormed` predicate, and the positive parser theorem

```lean
HtlcWire.txBytes_parse (h) (hw : h.WellFormed) :
  decTxCore (bL h.txBytes) = .ok (h.toTx, [])
```

This module is **purely additive**: it does not edit `SighashTargets` and it does
not restate that theorem.  It proves the strengthening in four layers.

1. **Field decomposition.**  The wire bytes are exactly the canonical
   version / input / output / locktime concatenation, with the single input and
   output exposed as `htlcIn`/`htlcOut` (`bL_txBytes_eq`).  A second
   decomposition, `decTxCore_prefix`, reduces the vendor parser on those bytes
   to the *only* two remaining steps: the script decoder and the locktime
   decoder.  All the framing is discharged once, symbolically.

2. **Round-trip, both directions.**  `txBytes_parse_full` lifts the existing
   `decTxCore` result to the "no trailing bytes" production entry point
   `decTxFull`, and `txBytes_roundtrip` records encode-then-decode and
   decode-then-encode agreement.

3. **Wire domain is exactly `WellFormed`.**  The new converse
   `wellFormed_of_wireDomain` together with the existing `wireDomain_toTx`
   gives `wellFormed_iff_wireDomain`: the parser's `wireDomain` obligations
   (32-byte prevout hash, `scriptPubKey.size ≤ MAX_SIZE`, `0 ≤ value`,
   `value < 2^63`) are *necessary and sufficient* for `WellFormed`, with the
   amount/width constants kept explicit.

4. **Negative cases.**
   * `parse_eq_toTx_iff`: the parser round-trips the wire value
     **iff** `valueSat.toNat < 2^63`.  Above that bound the vendor decoder folds
     the `uint64` through `u64ToAmt` and returns the *other* (two's-complement)
     amount, so the round-trip fails even though parsing itself succeeds:
     `parse_ne_toTx_of_value_ge`, `not_wireDomain_of_value_ge`.
   * `parse_truncated_at_version`, `parse_truncated_in_script`: truncation is a
     hard `.error .truncated`.
   * `parse_script_tooLong`: a declared script length `≥ 2^32` is rejected with
     `.compactSizeTooLong` (the `0xff` CompactSize branch is the only branch
     that enforces `MAX_SIZE`).
   * `oversizedWire_parse`: the honest converse failure — the
     `0xfe` CompactSize branch does *not* enforce `MAX_SIZE`, so a script of
     `MAX_SIZE + 1` bytes parses but is not in `wireDomain`.  This is the exact
     parser/serializer-domain gap; it is reported, not papered over.

Scope: these are statements about the vendor list-level parser and the
`HtlcWire` serializer only.  Nothing here claims a full transaction-validity or
consensus result.
-/

namespace LnLean.Proofs.WaveH.H11

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Serialization
open LnLean.Proofs.Channel.SighashTargets

/-! ## 1. Field-level decomposition of the wire transaction -/

/-- The single input of the HTLC-wire transaction. -/
def htlcIn (h : HtlcWire) : TxIn :=
  { prevout := ⟨h.commitmentTxid, h.commitmentOutputIndex⟩
    scriptSig := Script.empty
    sequence := h.sequence }

/-- The single output of the HTLC-wire transaction. -/
def htlcOut (h : HtlcWire) : TxOut :=
  { value := (h.valueSat.toNat : Int), scriptPubKey := ⟨h.scriptPubKey⟩ }

theorem toTx_eq (h : HtlcWire) :
    h.toTx = { version := h.version.toInt32
               vin := [htlcIn h]
               vout := [htlcOut h]
               locktime := h.locktime
               witness := [[]] } := rfl

/-- Everything the parser consumes before the script `CompactSize` prefix:
version, one input, one output value.  Written right-associated because `++`
is left-associative here and the parser/decoder lemmas match on a single
trailing append. -/
def prefixBytes (h : HtlcWire) : Bytes :=
  encU32L h.version ++ (encCSL 1 ++ (bL (serTxIn (htlcIn h)) ++
    (encCSL 1 ++ encU64L h.valueSat)))

/-- The serialized single output, with the value written as the raw `uint64`
bit pattern (`amtToU64`). -/
theorem bL_serTxOut_htlc (h : HtlcWire) :
    bL (serTxOut (htlcOut h)) =
      encU64L h.valueSat ++ encCSL h.scriptPubKey.size ++ bL h.scriptPubKey := by
  have hout : htlcOut h =
      ({ value := (h.valueSat.toNat : Int), scriptPubKey := ⟨h.scriptPubKey⟩ } : TxOut) := rfl
  rw [hout, bL_serTxOut]
  have hv : amtToU64 ((h.valueSat.toNat : Int)) = h.valueSat.toNat := by
    unfold amtToU64
    rw [if_neg (by omega : ¬ ((h.valueSat.toNat : Int) < 0))]
    simp
  have ho : UInt64.ofNat h.valueSat.toNat = h.valueSat := by
    rw [← UInt64.toNat_inj, u64_ofNat_toNat,
      Nat.mod_eq_of_lt h.valueSat.toNat_lt_size]
  rw [hv, ho]

/-- The wire bytes are the canonical base-transaction concatenation. -/
theorem bL_txBytes_eq (h : HtlcWire) :
    bL h.txBytes =
      prefixBytes h ++ (encCSL h.scriptPubKey.size ++
        (bL h.scriptPubKey ++ encU32L h.locktime)) := by
  rw [HtlcWire.txBytes, bL_serTx, toTx_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
    List.length_nil, Nat.reduceAdd, prefixBytes,
    bL_serTxOut_htlc, UInt32.toUInt32_toInt32, List.append_assoc]

/-- The transaction shape the parser produces once the script and locktime are
read: the same version/input as `h`, the raw decoded script, and the amount
folded through the vendor `u64ToAmt`. -/
def parsedWith (h : HtlcWire) (s : Script) (lt : UInt32) : Tx :=
  { version := h.version.toInt32
    vin := [htlcIn h]
    vout := [{ value := u64ToAmt h.valueSat.toNat, scriptPubKey := s }]
    locktime := lt
    witness := [[]] }

/-- `decN` at count one is a single element. -/
theorem decN_one {α : Type} (dec : Bytes → Except SerError (α × Bytes)) (l : Bytes) :
    decN dec 1 l = (do let (a, l1) ← dec l; .ok ([a], l1)) := by
  simp [decN]

/-- A value-position `TxOut` decode: `u64ToAmt` is applied to the raw wire
amount, and the script is read from the remainder. -/
theorem decTxOutL_value (v : UInt64) (rest : Bytes) :
    decTxOutL (encU64L v ++ rest) =
      (do let (s, l1) ← decScriptL rest
          .ok (({ value := u64ToAmt v.toNat, scriptPubKey := s } : TxOut), l1)) := by
  simp [decTxOutL, decU64L_encU64L, bindE_ok]

/-- **Parser inversion for the wire shape.**  With a 32-byte prevout hash, the
vendor parser on `prefixBytes h ++ tail` has exactly two steps left: the script
decoder on `tail`, then the 4-byte locktime.  Every framing check (CompactSize
counts, the zero-count marker branch, the input/output vector reads) is
discharged symbolically. -/
theorem decTxCore_prefix (h : HtlcWire) (htxid : h.commitmentTxid.size = 32)
    (tail : Bytes) :
    decTxCore (prefixBytes h ++ tail) =
      (do
        let (s, l1) ← decScriptL tail
        let (lt, l2) ← decU32L l1
        .ok (parsedWith h s lt, l2)) := by
  have hcs1 : ∀ rest : Bytes, decCS (encCSL 1 ++ rest) = .ok (1, rest) :=
    fun rest => decCS_encCSL 1 (by decide) rest
  have hin : ∀ rest : Bytes,
      decTxInL (bL (serTxIn (htlcIn h)) ++ rest) = .ok (htlcIn h, rest) :=
    fun rest => decTxInL_enc (htlcIn h) rest htxid (by
      show (Script.empty).bytes.size ≤ Bitcoin.Serialization.MAX_SIZE
      decide)
  have hvin : ∀ rest : Bytes,
      decN decTxInL 1 (bL (serTxIn (htlcIn h)) ++ rest) = .ok ([htlcIn h], rest) := by
    intro rest
    rw [decN_one]
    simp only [hin, bindE_ok]
  have hout : ∀ rest : Bytes,
      decN decTxOutL 1 (encU64L h.valueSat ++ rest) =
        (do let (s, l1) ← decScriptL rest
            .ok ([({ value := u64ToAmt h.valueSat.toNat, scriptPubKey := s } : TxOut)], l1)) := by
    intro rest
    rw [decN_one, decTxOutL_value]
    cases hs : decScriptL rest with
    | error e => simp [hs]
    | ok p =>
        obtain ⟨s, l1⟩ := p
        simp [hs]
  simp only [prefixBytes, decTxCore, decU32L_encU32L, hcs1, bindE_ok,
    decVinL, hvin, show (1 : Nat) ≠ 0 from by decide, if_false,
    Nat.reduceAdd, hout, parsedWith, List.append_assoc]
  cases hs : decScriptL tail with
  | error e => simp [hs]
  | ok p =>
      obtain ⟨s, l1⟩ := p
      simp [hs]

/-! ## 2. Wire domain is exactly `WellFormed` -/

/-- **Necessity of `WellFormed`.**  Every field bound required by the vendor
`wireDomain` predicate is exactly the corresponding `HtlcWire.WellFormed`
conjunct: 32-byte prevout hash, `scriptPubKey.size ≤ MAX_SIZE`, and the amount
in `[0, 2^63)`.  (`wireDomain_toTx` is the existing sufficient direction; this
is the converse, so the two predicates agree.) -/
theorem wellFormed_of_wireDomain (h : HtlcWire)
    (hw : Bitcoin.Serialization.wireDomain h.toTx) : h.WellFormed := by
  obtain ⟨hv0, hwlen, hvinc, hvoutc, hvin, hvout, hwit⟩ := hw
  have hvin' : htlcIn h ∈ h.toTx.vin := by
    rw [toTx_eq]; simp
  have hvout' : htlcOut h ∈ h.toTx.vout := by
    rw [toTx_eq]; simp
  obtain ⟨hhash, _⟩ := hvin (htlcIn h) hvin'
  obtain ⟨hsz, _, hval⟩ := hvout (htlcOut h) hvout'
  refine ⟨hhash, hsz, ?_⟩
  have hval' : ((h.valueSat.toNat : Int)) < 9223372036854775808 := hval
  have hnat : h.valueSat.toNat < 9223372036854775808 := by omega
  exact UInt64.lt_iff_toNat_lt.mpr (by simpa using hnat)

/-- **Exact wire-domain characterization**: the parser/serializer domain and
`WellFormed` coincide for the HTLC wire. -/
theorem wireDomain_iff_wellFormed (h : HtlcWire) :
    Bitcoin.Serialization.wireDomain h.toTx ↔ h.WellFormed :=
  ⟨wellFormed_of_wireDomain h, HtlcWire.wireDomain_toTx h⟩

/-- The three explicit field bounds, as a single reusable premise bundle. -/
theorem wellFormed_field_bounds (h : HtlcWire) (hw : h.WellFormed) :
    h.commitmentTxid.size = 32 ∧
      h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE ∧
      h.valueSat.toNat < 9223372036854775808 := by
  obtain ⟨hhash, hsz, hval⟩ := hw
  exact ⟨hhash, hsz, UInt64.lt_iff_toNat_lt.mp hval⟩

/-! ## 3. Parser round-trip, both directions -/

/-- **Round-trip at the production entry point.**  The existing positive
theorem `HtlcWire.txBytes_parse` gives the core parser result with empty
remainder; this lifts it to `decTxFull`, which is the "reject trailing bytes"
entry point used by `DecodeHexTx`. -/
theorem txBytes_parse_full (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.decTxFull (bL h.txBytes) = .ok h.toTx := by
  unfold Bitcoin.Serialization.decTxFull
  rw [HtlcWire.txBytes_parse h hw]
  simp

/-- Encode-then-decode and decode-then-encode agreement for the HTLC wire. -/
theorem txBytes_roundtrip (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.decTxFull (bL h.txBytes) = .ok h.toTx ∧
      bL h.txBytes = Bitcoin.Serialization.encTxL h.toTx :=
  ⟨txBytes_parse_full h hw, HtlcWire.txBytes_eq_encTxL h⟩

/-- The parsed transaction is the wire transaction whenever the amount is in
the `int64`-representable range; this is the field-level content of the
round-trip. -/
theorem parsedWith_toTx (h : HtlcWire)
    (hv : h.valueSat.toNat < 9223372036854775808) :
    parsedWith h ⟨h.scriptPubKey⟩ h.locktime = h.toTx := by
  rw [toTx_eq]
  simp [parsedWith, htlcOut, u64ToAmt, hv]

/-! ## 4. Parser characterization and the amount bound -/

/-- `u64ToAmt` is the two's-complement interpretation: either the raw value or
the raw value minus `2^64` (a negative `int64`). -/
theorem u64ToAmt_eq (u : Nat) :
    u64ToAmt u = (u : Int) ∨
      u64ToAmt u = (u : Int) - 18446744073709551616 := by
  unfold u64ToAmt
  by_cases h : u < 9223372036854775808
  · rw [if_pos h]
    exact Or.inl rfl
  · rw [if_neg h]
    exact Or.inr rfl

/-- The vendor parser's amount field is `u64ToAmt` of the raw wire `uint64`.
It agrees with the model value exactly on the `int64`-representable range. -/
theorem u64ToAmt_toNat_eq_iff (v : UInt64) :
    u64ToAmt v.toNat = (v.toNat : Int) ↔ v.toNat < 9223372036854775808 := by
  unfold u64ToAmt
  by_cases h : v.toNat < 9223372036854775808
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    have hne : (v.toNat : Int) - 18446744073709551616 ≠ (v.toNat : Int) := by
      omega
    exact ⟨fun heq => absurd heq hne, fun hc => absurd hc h⟩

/-- The 4-byte decoder at the end of the wire. -/
theorem decU32L_encU32L_nil (x : UInt32) :
    decU32L (encU32L x) = .ok (x, []) := by
  simpa using decU32L_encU32L x []

/-- **Parser characterization.**  With the script in the canonical
`CompactSize` domain, the vendor parser consumes the whole wire and returns a
transaction that differs from `h.toTx` only by the folded amount. -/
theorem txBytes_parse_form (h : HtlcWire) (htxid : h.commitmentTxid.size = 32)
    (hscr : h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE) :
    Bitcoin.Serialization.decTxCore (bL h.txBytes) =
      .ok (parsedWith h ⟨h.scriptPubKey⟩ h.locktime, []) := by
  rw [bL_txBytes_eq, decTxCore_prefix h htxid]
  simp only
  rw [decScriptL_enc (⟨h.scriptPubKey⟩) (encU32L h.locktime) hscr]
  simp only [bindE_ok, decU32L_encU32L_nil]

/-- **Value round-trip iff the amount is in range.**  The parser returns the
original transaction exactly when `valueSat.toNat < 2^63`. -/
theorem parse_eq_toTx_iff (h : HtlcWire) (htxid : h.commitmentTxid.size = 32)
    (hscr : h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE) :
    Bitcoin.Serialization.decTxCore (bL h.txBytes) = .ok (h.toTx, []) ↔
      h.valueSat.toNat < 9223372036854775808 := by
  rw [txBytes_parse_form h htxid hscr]
  constructor
  · intro heq
    have hp : parsedWith h ⟨h.scriptPubKey⟩ h.locktime = h.toTx := by
      simpa using heq
    have hval : u64ToAmt h.valueSat.toNat = (h.valueSat.toNat : Int) := by
      have hvout := congrArg (fun tx : Bitcoin.Data.Tx => tx.vout) hp
      simpa [parsedWith, toTx_eq, htlcOut] using hvout
    exact (u64ToAmt_toNat_eq_iff h.valueSat).mp hval
  · intro hvlt
    rw [parsedWith_toTx h hvlt]

/-- **Negative: out-of-range amount.**  Above `2^63` the parser still succeeds
but folds the value through `u64ToAmt`, so it does not return the wire
transaction.  This is a semantic rejection, not a parse error. -/
theorem parse_ne_toTx_of_value_ge (h : HtlcWire)
    (htxid : h.commitmentTxid.size = 32)
    (hscr : h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE)
    (hv : 9223372036854775808 ≤ h.valueSat.toNat) :
    Bitcoin.Serialization.decTxCore (bL h.txBytes) ≠ .ok (h.toTx, []) := by
  intro heq
  have := (parse_eq_toTx_iff h htxid hscr).mp heq
  omega

/-- The `UInt64` form of the negative amount case, matching the `WellFormed`
field's comparison. -/
theorem parse_ne_toTx_of_value_ge_uint64 (h : HtlcWire)
    (htxid : h.commitmentTxid.size = 32)
    (hscr : h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE)
    (hv : (9223372036854775808 : UInt64) ≤ h.valueSat) :
    Bitcoin.Serialization.decTxCore (bL h.txBytes) ≠ .ok (h.toTx, []) := by
  refine parse_ne_toTx_of_value_ge h htxid hscr ?_
  have := UInt64.le_iff_toNat_le.mp hv
  simpa using this

/-- `WellFormed` fails when the amount is out of range: the explicit
wire-domain consequence of the negative above. -/
theorem not_wireDomain_of_value_ge (h : HtlcWire)
    (hv : (9223372036854775808 : UInt64) ≤ h.valueSat) :
    ¬ Bitcoin.Serialization.wireDomain h.toTx := by
  intro hw
  have hwf := (wellFormed_of_wireDomain h hw).2.2
  rw [UInt64.lt_iff_toNat_lt] at hwf
  have hlit : (9223372036854775808 : UInt64).toNat = 9223372036854775808 := by
    decide
  rw [hlit] at hwf
  have hge := UInt64.le_iff_toNat_le.mp hv
  omega

/-- `WellFormed` fails when the script exceeds `MAX_SIZE`. -/
theorem not_wireDomain_of_script_oversize (h : HtlcWire)
    (hsz : Bitcoin.Serialization.MAX_SIZE < h.scriptPubKey.size) :
    ¬ Bitcoin.Serialization.wireDomain h.toTx := by
  intro hw
  have := (wellFormed_of_wireDomain h hw).2.1
  omega

/-! ## 5. Truncated inputs -/

/-- A bare 4-byte version has no `CompactSize` input count: hard truncation. -/
theorem decTxCore_truncated_at_version (x : UInt32) :
    Bitcoin.Serialization.decTxCore (encU32L x) = .error .truncated := by
  simp [decTxCore, decU32L, decCS, encU32L]

/-- **Truncation at the version field.**  Cutting the wire after the version
is a `.truncated` parse error. -/
theorem parse_truncated_at_version (h : HtlcWire) :
    Bitcoin.Serialization.decTxCore ((bL h.txBytes).take 4) = .error .truncated := by
  rw [bL_txBytes_eq]
  have htake : (prefixBytes h ++ (encCSL h.scriptPubKey.size ++
      (bL h.scriptPubKey ++ encU32L h.locktime))).take 4 = encU32L h.version := by
    simp [prefixBytes, encU32L]
  rw [htake]
  exact decTxCore_truncated_at_version h.version

/-- `compactSizeWidth` is the length of the canonical `CompactSize` encoding. -/
theorem length_encCSL (n : Nat) : (encCSL n).length = compactSizeWidth n := by
  rw [← bL_compactSizeEnc]
  simp [bL, compactSizeEnc_size]

/-- A `CompactSize`-prefixed script with no payload is a hard truncation. -/
theorem decScriptL_encCSL_nil (n : Nat) (hpos : 0 < n)
    (hn : n ≤ Bitcoin.Serialization.MAX_SIZE) :
    decScriptL (encCSL n) = .error .truncated := by
  have hcs0 : decCS (encCSL n) = .ok (n, []) := by
    simpa using decCS_encCSL n hn []
  rw [decScriptL, decScriptBL, hcs0]
  simp [bindE_ok, decBytesL, hpos]

/-- **Truncation inside the script payload.**  Cutting the wire exactly after
the script `CompactSize` prefix leaves the declared script bytes missing, and
the parser reports `.truncated`. -/
theorem parse_truncated_in_script (h : HtlcWire)
    (htxid : h.commitmentTxid.size = 32) (hpos : 0 < h.scriptPubKey.size)
    (hM : h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE) :
    Bitcoin.Serialization.decTxCore
        ((bL h.txBytes).take ((prefixBytes h).length +
          compactSizeWidth h.scriptPubKey.size)) = .error .truncated := by
  have htake : (prefixBytes h ++ (encCSL h.scriptPubKey.size ++
      (bL h.scriptPubKey ++ encU32L h.locktime))).take
        ((prefixBytes h).length + compactSizeWidth h.scriptPubKey.size)
      = prefixBytes h ++ encCSL h.scriptPubKey.size := by
    rw [List.take_append]
    have h1 : (prefixBytes h).length ≤ (prefixBytes h).length +
        compactSizeWidth h.scriptPubKey.size := Nat.le_add_right _ _
    rw [List.take_of_length_le h1]
    have h2 : (prefixBytes h).length + compactSizeWidth h.scriptPubKey.size -
        (prefixBytes h).length = compactSizeWidth h.scriptPubKey.size := by omega
    rw [h2, ← length_encCSL h.scriptPubKey.size, List.take_left]
  rw [bL_txBytes_eq, htake, decTxCore_prefix h htxid]
  simp [decScriptL_encCSL_nil h.scriptPubKey.size hpos hM]

/-! ## 6. Oversized declared script lengths

The vendor `decCS` only enforces `MAX_SIZE` on the `0xff` branch.  Therefore a
declared script length above `2^32` is rejected with
`.compactSizeTooLong`, while a length in `(MAX_SIZE, 2^32)` is accepted by the
parser even though the transaction then fails `wireDomain`.  Both facts are
mechanized: the first as the intended negative case, the second as the honest
domain gap. -/

/-- A declared script length of `2^32` is rejected: the `0xff` `CompactSize`
branch is the one that enforces `MAX_SIZE`. -/
theorem decScriptL_declared_tooLong :
    decScriptL (encCSL 4294967296) = .error .compactSizeTooLong := by
  simp [decScriptL, decScriptBL, decCS, encCSL, encU64L,
    Bitcoin.Serialization.MAX_SIZE]

/-- **Oversized-declaration negative.**  A wire whose script length prefix
declares `2^32` bytes is rejected with `.compactSizeTooLong`. -/
theorem parse_script_tooLong (h : HtlcWire)
    (htxid : h.commitmentTxid.size = 32) :
    Bitcoin.Serialization.decTxCore (prefixBytes h ++ encCSL 4294967296) =
      .error .compactSizeTooLong := by
  rw [decTxCore_prefix h htxid]
  simp [decScriptL_declared_tooLong]

/-- The wide `CompactSize` round-trip: the `0xfe` branch accepts every
`n ≤ 0xffffffff` without a `MAX_SIZE` check. -/
theorem decCS_encCSL_wide (n : Nat) (h1 : ¬ n < 0xfd) (h2 : ¬ n ≤ 0xffff)
    (h3 : n ≤ 0xffffffff) (rest : Bytes) :
    decCS (encCSL n ++ rest) = .ok (n, rest) := by
  unfold encCSL
  rw [if_neg h1, if_neg h2, if_pos h3]
  simp only [List.cons_append, List.append_assoc, decCS]
  have hlt : ¬ ((0xfe : UInt8).toNat < 0xfd) := by decide
  have heq0 : ¬ ((0xfe : UInt8) = (0xfd : UInt8)) := by decide
  have heq : (0xfe : UInt8) = (0xfe : UInt8) := rfl
  simp only [hlt, if_false, heq0, heq, if_true, encU32L, List.cons_append,
    List.append_assoc, List.nil_append]
  have hval : n.toUInt32.toUInt8.toNat
      + 256 * ((n.toUInt32 >>> 8 : UInt32).toUInt8.toNat
        + 256 * ((n.toUInt32 >>> 16 : UInt32).toUInt8.toNat
          + 256 * (n.toUInt32 >>> 24 : UInt32).toUInt8.toNat)) = n := by
    have hV : n.toUInt32.toUInt8.toNat
        + 256 * ((n.toUInt32 >>> 8 : UInt32).toUInt8.toNat
          + 256 * ((n.toUInt32 >>> 16 : UInt32).toUInt8.toNat
            + 256 * (n.toUInt32 >>> 24 : UInt32).toUInt8.toNat))
        = n.toUInt32.toNat := by
      rw [u32_b0, u32_b1, u32_b2, u32_b3]
      have hx : n.toUInt32.toNat < 4294967296 := n.toUInt32.toNat_lt_size
      omega
    rw [hV, u32_ofNat_toNat, Nat.mod_eq_of_lt (by omega)]
  have hbig : ¬ (n.toUInt32.toUInt8.toNat
      + 256 * ((n.toUInt32 >>> 8 : UInt32).toUInt8.toNat
        + 256 * ((n.toUInt32 >>> 16 : UInt32).toUInt8.toNat
          + 256 * (n.toUInt32 >>> 24 : UInt32).toUInt8.toNat)) < 0x10000) := by
    rw [hval]
    omega
  rw [if_neg hbig, hval]

/-- A script decoder law for the wide `0xfe` domain (no `MAX_SIZE` premise). -/
theorem decScriptL_enc_wide (b : ByteArray) (rest : Bytes) (n : Nat)
    (hn : b.size = n) (h16 : 0x10000 ≤ n) (hu : n ≤ 0xffffffff) :
    decScriptL (encCSL n ++ (bL b ++ rest)) = .ok (⟨b⟩, rest) := by
  rw [← hn]
  have h16' : 0x10000 ≤ b.size := by rw [hn]; exact h16
  have hu' : b.size ≤ 0xffffffff := by rw [hn]; exact hu
  have hcs : ∀ r : Bytes, decCS (encCSL b.size ++ r) = .ok (b.size, r) :=
    fun r => decCS_encCSL_wide b.size (by omega) (by omega) hu' r
  simp only [decScriptL, decScriptBL]
  rw [hcs]
  simp only [bindE_ok]
  rw [decBytesL_enc (bL b) b.size (by simp [bL]) _]
  simp only [bindE_ok, bytesOfList_bL]

/-- The parser characterization with an explicit script-decoder premise, so it
can be instantiated both in the canonical and in the wide domain. -/
theorem txBytes_parse_form_of_script (h : HtlcWire)
    (htxid : h.commitmentTxid.size = 32)
    (hscr : decScriptL (encCSL h.scriptPubKey.size ++
      (bL h.scriptPubKey ++ encU32L h.locktime)) =
      .ok (⟨h.scriptPubKey⟩, encU32L h.locktime)) :
    Bitcoin.Serialization.decTxCore (bL h.txBytes) =
      .ok (parsedWith h ⟨h.scriptPubKey⟩ h.locktime, []) := by
  rw [bL_txBytes_eq, decTxCore_prefix h htxid, hscr]
  simp [decU32L_encU32L_nil]

/-- A script of `MAX_SIZE + 1` zero bytes. -/
def fillerByteArray (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

theorem fillerByteArray_size (n : Nat) : (fillerByteArray n).size = n := by
  simp only [fillerByteArray, ByteArray.size, Array.size_replicate]

/-- The concrete oversized counterexample wire: `MAX_SIZE + 1` script bytes,
one satoshi amount, canonical everything else. -/
def oversizedWire : HtlcWire :=
  { version := 2
    commitmentTxid := fillerByteArray 32
    commitmentOutputIndex := 0
    sequence := 0xffffffff
    valueSat := 1000
    scriptPubKey := fillerByteArray (Bitcoin.Serialization.MAX_SIZE + 1)
    locktime := 0 }

theorem oversizedWire_commitmentTxid_size :
    oversizedWire.commitmentTxid.size = 32 := by
  simp [oversizedWire, fillerByteArray_size]

theorem oversizedWire_scriptPubKey_size :
    oversizedWire.scriptPubKey.size = Bitcoin.Serialization.MAX_SIZE + 1 := by
  simp [oversizedWire, fillerByteArray_size]

/-- **Honest domain gap.**  The oversized wire parses to exactly `toTx` even
though it is not `WellFormed` (and not in `wireDomain`): the vendor `0xfe`
`CompactSize` branch does not enforce `MAX_SIZE`. -/
theorem oversizedWire_parse :
    Bitcoin.Serialization.decTxCore (bL oversizedWire.txBytes) =
      .ok (oversizedWire.toTx, []) := by
  have hscr : decScriptL (encCSL oversizedWire.scriptPubKey.size ++
      (bL oversizedWire.scriptPubKey ++ encU32L oversizedWire.locktime)) =
      .ok (⟨oversizedWire.scriptPubKey⟩, encU32L oversizedWire.locktime) := by
    rw [oversizedWire_scriptPubKey_size]
    exact decScriptL_enc_wide oversizedWire.scriptPubKey
      (encU32L oversizedWire.locktime)
      (Bitcoin.Serialization.MAX_SIZE + 1)
      oversizedWire_scriptPubKey_size
      (by decide)
      (by decide)
  rw [txBytes_parse_form_of_script oversizedWire
    oversizedWire_commitmentTxid_size hscr]
  have hpt : parsedWith oversizedWire ⟨oversizedWire.scriptPubKey⟩
      oversizedWire.locktime = oversizedWire.toTx :=
    parsedWith_toTx _ (by decide)
  rw [hpt]

theorem oversizedWire_not_wellFormed : ¬ oversizedWire.WellFormed := by
  intro hw
  have hsz := hw.2.1
  rw [oversizedWire_scriptPubKey_size] at hsz
  omega

/-- The parser/serializer domain is strictly larger than `wireDomain` on the
`0xfe` `CompactSize` branch. -/
theorem oversizedWire_not_wireDomain :
    ¬ Bitcoin.Serialization.wireDomain oversizedWire.toTx := by
  intro hw
  exact oversizedWire_not_wellFormed (wellFormed_of_wireDomain _ hw)

end LnLean.Proofs.WaveH.H11
