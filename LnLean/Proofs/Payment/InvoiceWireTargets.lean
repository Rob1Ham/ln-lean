import LnLean.Payment.Invoice
import LnLean.Wire.BigSize

/-!
# LnLean.Proofs.Payment.InvoiceWireTargets

English claim.  This module adds a self-contained, canonical wire/serialization
layer around the BOLT 11 invoice model in `LnLean.Payment.Invoice`.  The layer
is deliberately *pre-bech32*: it models the human-readable prefix and the
tagged-field container as a canonical field list, not the bech32 charset,
checksum, or signable-digest bytes.  It covers the fields the model actually
has: the network prefix, the optional millisatoshi amount, the 35-bit
timestamp, the payment hash (`p`), the payment secret (`s`), the payee key
(`n`), the expiry (`x`), the minimum final CLTV delta (`c`), the feature bits,
and an additive flat route-hint model (`r`).

What is proved here.

1. **Canonical scalar codecs.**  Network prefixes are injective and round-trip;
   millisatoshi amounts and 64-bit integers have canonical big-endian codecs;
   the three modelled feature booleans have an injective bitfield codec; a
   route-hint hop (packed `short_channel_id`, fee base, proportional fee, CLTV
   delta) has an 18-byte canonical codec.
2. **Field/record round trip.**  `print` emits a canonical header plus the
   fixed-order field list `p, s, n, x, c, f, r*`; `parse` accepts exactly that
   canonical order and rejects wrong tags, wrong fixed lengths, non-canonical
   integers, and duplicate/extra fields.  For every `WireInvoice.Canonical`
   invoice, `parse (print w) = some w`; `print` is injective on canonical
   invoices.
3. **Projection to the core model.**  `ofInvoice` embeds every core invoice
   into the wire model (with no route hints); `toInvoice` projects back with a
   caller-supplied description.  `toInvoice (ofInvoice i) i.description = i`,
   and a canonical wire invoice projects to a structurally valid core invoice.
4. **Binding and the exact hash-image boundary.**  Payment-secret equality is
   exactly byte equality and survives the wire codec.  A preimage determines
   its payment hash unconditionally, and determines at most one preimage only
   under an explicit injectivity hypothesis.  The hash image is not the
   preimage: without injectivity a constant hash gives two distinct preimages
   for one image, and a 31-byte (invalid) preimage still commits.  The converse
   direction is *not* available from the algebraic model.
5. **Signature is not payment.**  A concrete invoice whose payment hash lies
   outside the image of a constant hash can pass the model's `Invoice.verify`
   with an always-accepting checker while no preimage commits.  This is the
   mechanized counterexample to the common mistake of treating an invoice
   signature as proof of payment.
6. **Concrete witnesses.**  One fully populated invoice witness (with a route
   hint) round-trips and projects to a valid invoice, and malformed invoices
   (a 31-byte payment hash and a duplicate `p` field) are rejected.

BOLT sections.
* BOLT 11 "Human-Readable Part": network prefix and optional amount;
  "Data Part": 35-bit timestamp and 65-byte compact signature; "Tagged
  Fields": `p`, `s`, `d`/`h`, `n`, `x`, `c`, `9` (features), `r` (route
  hints); "Payer / Payee Requirements": expiry.
* BOLT 9 feature bits 8/9 (`var_onion_optin`, modelled as bit 8),
  14/15 (`payment_secret`, modelled as bit 14), and 16/17 (`basic_mpp`,
  modelled as bit 16).  The optional/mandatory pairing is not modelled; the
  codec uses one canonical bit per modelled boolean.
* BOLT 7 `short_channel_id` packing: `block << 40 | tx << 16 | output`.
* BOLT 4 "Final Node": the payment hash is the hash image the recipient
  checks, and the payment preimage is the proof of payment.

BOLT line anchors (pinned BOLTs commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`).
* `refs/bolts/11-payment-encoding.md:47-87` HRP and optional amount.
* `refs/bolts/11-payment-encoding.md:104-131` timestamp/signature data part.
* `refs/bolts/11-payment-encoding.md:133-163` tagged fields and lengths.
* `refs/bolts/11-payment-encoding.md:165-205` reader/writer field checks.
* `refs/bolts/11-payment-encoding.md:303-326` feature bits.
* `refs/bolts/11-payment-encoding.md:344-360` expiry.
* `refs/bolts/07-routing-gossip.md` `short_channel_id`.
* `refs/bolts/09-features.md:42-43` `payment_secret`, `basic_mpp`.
* `refs/bolts/04-onion-routing.md:1528-1545` final-node amount/secret checks.

rust-lightning anchors (commit `fe4900930c6bd5786ec4203274d7cf312776a5a6`).
* `lightning-invoice/src/lib.rs:272` `struct Bolt11Invoice`.
* `lightning-invoice/src/lib.rs:527` `enum TaggedField`; `:613` tag constants.
* `lightning-invoice/src/lib.rs:680`/`:1662` amount accessor.
* `lightning-invoice/src/lib.rs:1322` `check_field_counts`; `:1357`
  `check_payment_secret`; `:1376` `check_amount`.
* `lightning-invoice/src/lib.rs:1529` `expires_at`; `:1534` `expiry_time`.
* `lightning-types/src/payment.rs:23` `PaymentHash([u8; 32])`;
  `:49` `PaymentPreimage([u8; 32])`; `:82` `PaymentSecret([u8; 32])`.

What is explicitly NOT modelled.
* bech32/charset encoding, the checksum, HRP string parsing, and the
  signable-digest byte construction.  `parse`/`print` operate on a canonical
  *field list*; the network prefix is a token, not a decoded bech32 string.
* Amount multipliers and decimal rendering.  The header carries the
  already-parsed millisatoshi amount; the canonical amount codec is a helper
  for a future HRP encoder.
* UTF-8 validation of the direct description.  Description is not part of
  the wire record; `toInvoice` takes it as an explicit argument
  (`DescriptionShape` records the only wire-relevant conjunct, the 32-byte
  `h` digest).
* Recoverable ECDSA and signature unforgeability.  `Invoice.verify` keeps the
  checker as a parameter; this module proves *no* computational signature or
  security claim.  Signature acceptance is explicitly separated from payment
  evidence.
* Computational preimage resistance.  `preimage_unique_of_injective` is
  conditional on `Function.Injective hash`; the counterexamples show the
  algebraic hash relation alone is insufficient.  No concrete SHA-256,
  probability, or query bound is asserted.
* Route-hint grouping and preference ordering.  Route hints are a flat ordered
  list of hops; per-hint grouping is a documented model gap.
-/

namespace LnLean.Proofs.Payment.InvoiceWireTargets

open LnLean
open LnLean.Payment
open LnLean.Wire

set_option autoImplicit false

/-! ## 1. Canonical scalar codecs -/

/-- Addition and division helper: the low `k`-bit part does not affect the
quotient when it is below `k`. -/
theorem div_add_mul {a b k : Nat} (hb : b < k) (hk : 0 < k) :
    (a * k + b) / k = a := by
  rw [Nat.mul_comm a k, Nat.mul_add_div hk, Nat.div_eq_of_lt hb]
  simp

/-- Addition and modulo helper: the high part is a multiple of `k`. -/
theorem mod_add_mul {a b k : Nat} (hb : b < k) : (a * k + b) % k = b := by
  rw [Nat.mul_comm a k, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hb

/-- The BOLT 11 human-readable prefix is injective across the four modelled
networks.  This is the wire-level form of `Network.code_injective`. -/
def prefixOf (n : Network) : String := n.hrpPrefix

/-- Recognise a modelled BOLT 11 prefix.  Unknown prefixes are rejected. -/
def networkOfPrefix : String → Option Network
  | "lnbc" => some .mainnet
  | "lntb" => some .testnet
  | "lntbs" => some .signet
  | "lnbcrt" => some .regtest
  | _ => none

/-- **Prefix round trip.**  Every modelled network's prefix is recognised as
that network. -/
theorem networkOfPrefix_prefixOf (n : Network) :
    networkOfPrefix (prefixOf n) = some n := by
  cases n <;> rfl

/-- **Prefix injectivity.**  Distinct networks have distinct BOLT 11
prefixes. -/
theorem prefixOf_injective : Function.Injective prefixOf := by
  intro a b h
  cases a <;> cases b <;> simp [prefixOf, Network.hrpPrefix] at h ⊢

/-- A canonical fixed-width `Nat` payload: big-endian, exactly eight bytes. -/
def encodeNat (n : Nat) : ByteArray := beBytes n 8

/-- Decode an eight-byte canonical `Nat` payload.  Other lengths are
rejected. -/
def decodeNat (b : ByteArray) : Option Nat :=
  if b.size = 8 then some (decodeBE b) else none

/-- **`Nat` codec round trip.**  An eight-byte payload recovers exactly the
value encoded, provided the value fits in 64 bits. -/
theorem decodeNat_encodeNat {n : Nat} (h : n < 2 ^ 64) :
    decodeNat (encodeNat n) = some n := by
  have hlt : n < 256 ^ 8 := by
    rwa [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
  unfold decodeNat encodeNat
  rw [beBytes_size]
  simp [decodeBE_beBytes_of_lt n 8 hlt]

/-- The canonical amount payload: empty for an absent amount, eight
big-endian bytes for a present amount. -/
def encodeAmount : Option Msat → ByteArray
  | none => ByteArray.empty
  | some a => beBytes a.val 8

/-- Decode the canonical amount payload.  Both the absent form (empty) and
the present form (eight bytes) are accepted; any other length is rejected. -/
def decodeAmount (b : ByteArray) : Option (Option Msat) :=
  if b.size = 0 then some none
  else if b.size = 8 then some (some ⟨decodeBE b⟩)
  else none

/-- **Absent amount round trip.** -/
theorem decodeAmount_encodeAmount_none :
    decodeAmount (encodeAmount none) = some none := by
  unfold decodeAmount encodeAmount
  simp

/-- **Present amount round trip.**  Under the explicit 64-bit bound, the
canonical amount payload recovers the amount exactly. -/
theorem decodeAmount_encodeAmount_some {a : Msat} (h : a.val < 2 ^ 64) :
    decodeAmount (encodeAmount (some a)) = some (some a) := by
  have hlt : a.val < 256 ^ 8 := by
    rwa [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
  unfold decodeAmount encodeAmount
  rw [beBytes_size]
  simp [decodeBE_beBytes_of_lt a.val 8 hlt]

/-! ### Feature bits -/

/-- Bit 14 = `payment_secret`, bit 16 = `basic_mpp`, bit 8 =
`var_onion_optin`.  The BOLT 9 optional/mandatory pairs are collapsed to one
canonical bit per modelled boolean; the pairing is a documented gap. -/
def featureBits (f : InvoiceFeatures) : Nat :=
  (if f.paymentSecretRequired then 2 ^ 14 else 0) +
  (if f.basicMpp then 2 ^ 16 else 0) +
  (if f.variableLengthOnion then 2 ^ 8 else 0)

/-- Decode the three modelled feature bits. -/
def featuresOfBits (n : Nat) : InvoiceFeatures :=
  { paymentSecretRequired := n / 2 ^ 14 % 2 = 1
    basicMpp := n / 2 ^ 16 % 2 = 1
    variableLengthOnion := n / 2 ^ 8 % 2 = 1 }

/-- The modelled feature bits occupy only the low 17 bits. -/
theorem featureBits_lt (f : InvoiceFeatures) : featureBits f < 2 ^ 17 := by
  cases f with
  | mk ps mpp vo => cases ps <;> cases mpp <;> cases vo <;> decide

/-- **Feature bitfield round trip.** -/
theorem featuresOfBits_featureBits (f : InvoiceFeatures) :
    featuresOfBits (featureBits f) = f := by
  cases f with
  | mk ps mpp vo => cases ps <;> cases mpp <;> cases vo <;> decide

/-- **Feature bitfield injectivity.** -/
theorem featureBits_injective : Function.Injective featureBits := by
  intro a b h
  have ha := featuresOfBits_featureBits a
  have hb := featuresOfBits_featureBits b
  rw [h] at ha
  exact ha.symm.trans hb

/-- Canonical four-byte feature payload. -/
def encodeFeatures (f : InvoiceFeatures) : ByteArray := beBytes (featureBits f) 4

/-- Decode a canonical four-byte feature payload. -/
def decodeFeatures (b : ByteArray) : Option InvoiceFeatures :=
  if b.size = 4 then some (featuresOfBits (decodeBE b)) else none

/-- **Feature payload round trip.** -/
theorem decodeFeatures_encodeFeatures (f : InvoiceFeatures) :
    decodeFeatures (encodeFeatures f) = some f := by
  have hlt : featureBits f < 256 ^ 4 := by
    have h := featureBits_lt f
    rw [show (256 : Nat) ^ 4 = 2 ^ 32 by decide]
    omega
  simp [decodeFeatures, encodeFeatures, beBytes_size,
    decodeBE_beBytes_of_lt (featureBits f) 4 hlt, featuresOfBits_featureBits]

/-! ### Route-hint hops -/

/-- One hop of a private route hint.  The fee fields are the BOLT 11 `r`
fields: base fee in millisatoshis, proportional fee in millionths, and the
CLTV delta.  Route-hint grouping/preference ordering is not modelled. -/
structure RouteHintHop where
  channel : ShortChannelId
  feeBaseMsat : Nat
  feeProportionalMillionths : Nat
  cltvExpiryDelta : Nat
deriving Repr, DecidableEq, BEq

namespace RouteHintHop

/-- Canonicality of a hop: the short-channel-id is in range and each numeric
field fits its fixed wire width (32, 32, and 16 bits). -/
def Valid (h : RouteHintHop) : Prop :=
  h.channel.Valid ∧ h.feeBaseMsat < 2 ^ 32 ∧
    h.feeProportionalMillionths < 2 ^ 32 ∧ h.cltvExpiryDelta < 2 ^ 16

end RouteHintHop

/-- Unpack a 64-bit `short_channel_id` into its BOLT 7 fields. -/
def scidOfU64 (u : Nat) : ShortChannelId :=
  { block := u / 1099511627776
    txIndex := (u / 65536) % 16777216
    outputIndex := u % 65536 }

/-- **Short-channel-id round trip.**  For a valid BOLT 7 id, unpacking its
packed 64-bit form returns the original id. -/
theorem scidOfU64_toU64 {s : ShortChannelId} (h : s.Valid) :
    scidOfU64 s.toU64 = s := by
  rcases s with ⟨block, tx, out⟩
  rcases h with ⟨hb, ht, ho⟩
  have hb' : block < 16777216 := by simpa using hb
  have ht' : tx < 16777216 := by simpa using ht
  have ho' : out < 65536 := by simpa using ho
  unfold scidOfU64 ShortChannelId.toU64
  have hdec : block * 1099511627776 + tx * 65536 + out =
      (block * 16777216 + tx) * 65536 + out := by omega
  rw [hdec]
  have hmod : ((block * 16777216 + tx) * 65536 + out) % 65536 = out := by
    rw [Nat.mul_comm ((block * 16777216 + tx)) 65536, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt ho'
  have hdiv : ((block * 16777216 + tx) * 65536 + out) / 65536 =
      block * 16777216 + tx := by
    rw [Nat.mul_comm ((block * 16777216 + tx)) 65536, Nat.mul_add_div (by decide),
      Nat.div_eq_of_lt ho']
    simp
  rw [hmod, hdiv]
  have hmod2 : (block * 16777216 + tx) % 16777216 = tx := by
    rw [Nat.mul_comm block 16777216, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt ht'
  have hdiv2 : (block * 16777216 + tx) / 16777216 = block := by
    rw [Nat.mul_comm block 16777216, Nat.mul_add_div (by decide), Nat.div_eq_of_lt ht']
    simp
  rw [hmod2]
  have hdiv3 : ((block * 16777216 + tx) * 65536 + out) / 1099511627776 = block := by
    rw [show (1099511627776 : Nat) = 65536 * 16777216 by decide]
    rw [← Nat.div_div_eq_div_mul]
    rw [hdiv, hdiv2]
  rw [hdiv3]

/-- Pack a hop into the 144-bit canonical layout
`scid(64) | fee_base(32) | fee_prop(32) | cltv(16)`. -/
def hopPacked (h : RouteHintHop) : Nat :=
  h.channel.toU64 * 2 ^ 80 + h.feeBaseMsat * 2 ^ 48 +
    h.feeProportionalMillionths * 2 ^ 16 + h.cltvExpiryDelta

/-- **Packed-hop bound.**  A valid hop packs below `2^144`. -/
theorem hopPacked_lt {h : RouteHintHop} (hh : h.Valid) : hopPacked h < 2 ^ 144 := by
  rcases hh with ⟨hsc, hfb, hfp, hcltv⟩
  have hsc' : h.channel.toU64 < 2 ^ 64 := by
    have := ShortChannelId.toU64_lt_of_valid h.channel hsc
    simpa using this
  unfold hopPacked
  omega

/-- **Packed-hop decomposition.**  The four fixed-width components are
recovered by the corresponding quotient/modulus operations. -/
theorem decode_hopPacked {h : RouteHintHop} (hh : h.Valid) :
    (hopPacked h % 2 ^ 16 = h.cltvExpiryDelta) ∧
    ((hopPacked h / 2 ^ 16) % 2 ^ 32 = h.feeProportionalMillionths) ∧
    ((hopPacked h / 2 ^ 16 / 2 ^ 32) % 2 ^ 32 = h.feeBaseMsat) ∧
    (hopPacked h / 2 ^ 16 / 2 ^ 32 / 2 ^ 32 = h.channel.toU64) := by
  rcases hh with ⟨hsc, hfb, hfp, hcltv⟩
  have hdecomp : hopPacked h =
      ((h.channel.toU64 * 2 ^ 32 + h.feeBaseMsat) * 2 ^ 32 +
        h.feeProportionalMillionths) * 2 ^ 16 + h.cltvExpiryDelta := by
    unfold hopPacked; omega
  have hstep1 : hopPacked h / 2 ^ 16 =
      (h.channel.toU64 * 2 ^ 32 + h.feeBaseMsat) * 2 ^ 32 +
        h.feeProportionalMillionths := by
    rw [hdecomp]; exact div_add_mul hcltv (by decide)
  have hstep2 : hopPacked h / 2 ^ 16 / 2 ^ 32 =
      h.channel.toU64 * 2 ^ 32 + h.feeBaseMsat := by
    rw [hstep1]; exact div_add_mul hfp (by decide)
  have hstep3 : hopPacked h / 2 ^ 16 / 2 ^ 32 / 2 ^ 32 =
      h.channel.toU64 := by
    rw [hstep2]; exact div_add_mul hfb (by decide)
  refine ⟨?_, ?_, ?_, hstep3⟩
  · rw [hdecomp, mod_add_mul hcltv]
  · rw [hstep1, mod_add_mul hfp]
  · rw [hstep2, mod_add_mul hfb]

/-- Canonical 18-byte hop payload. -/
def encodeHop (h : RouteHintHop) : ByteArray := beBytes (hopPacked h) 18

/-- Decode an 18-byte hop payload.  Other lengths are rejected. -/
def decodeHop (b : ByteArray) : Option RouteHintHop :=
  if b.size = 18 then
    let n := decodeBE b
    some { channel := scidOfU64 (n / 2 ^ 16 / 2 ^ 32 / 2 ^ 32)
           feeBaseMsat := (n / 2 ^ 16 / 2 ^ 32) % 2 ^ 32
           feeProportionalMillionths := (n / 2 ^ 16) % 2 ^ 32
           cltvExpiryDelta := n % 2 ^ 16 }
  else none

/-- The canonical hop payload always has 18 bytes. -/
theorem encodeHop_size (h : RouteHintHop) : (encodeHop h).size = 18 := by
  unfold encodeHop; exact beBytes_size _ _

/-- **Hop codec round trip.**  Decoding the canonical encoding of a valid hop
returns that hop. -/
theorem decodeHop_encodeHop {h : RouteHintHop} (hh : h.Valid) :
    decodeHop (encodeHop h) = some h := by
  rcases hh with ⟨hsc, hfb, hfp, hcltv⟩
  have hlt : hopPacked h < 256 ^ 18 := by
    have := hopPacked_lt ⟨hsc, hfb, hfp, hcltv⟩
    rwa [show (256 : Nat) ^ 18 = 2 ^ 144 by decide]
  have hdec : decodeBE (encodeHop h) = hopPacked h := by
    unfold encodeHop
    exact decodeBE_beBytes_of_lt _ _ hlt
  have hcomp := decode_hopPacked ⟨hsc, hfb, hfp, hcltv⟩
  have hsc' : scidOfU64 (hopPacked h / 2 ^ 16 / 2 ^ 32 / 2 ^ 32) = h.channel := by
    rw [hcomp.2.2.2]; exact scidOfU64_toU64 hsc
  simp [decodeHop, encodeHop_size, hdec, hcomp.1, hcomp.2.1, hcomp.2.2.1, hsc']

/-! ## 2. The canonical field container -/

/-- A tagged field with an opaque byte payload.  The type is a `Nat` using
the BOLT 11 tag numbers; parsing enforces the canonical order below. -/
structure WireField where
  tag : Nat
  payload : ByteArray
deriving Repr, DecidableEq, BEq

/-- BOLT 11 `p`. -/
def paymentHashTag : Nat := 1
/-- BOLT 11 `s`. -/
def paymentSecretTag : Nat := 16
/-- BOLT 11 `n`. -/
def payeeTag : Nat := 19
/-- BOLT 11 `x`. -/
def expiryTag : Nat := 6
/-- BOLT 11 `c`. -/
def minFinalCltvTag : Nat := 24
/-- BOLT 11 `9` (features). -/
def featuresTag : Nat := 5
/-- BOLT 11 `r` (private route). -/
def routeHintTag : Nat := 3

def paymentHashField (p : PaymentHash) : WireField :=
  { tag := paymentHashTag, payload := p.bytes }
def paymentSecretField (s : PaymentSecret) : WireField :=
  { tag := paymentSecretTag, payload := s.bytes }
def payeeField (p : PubKey) : WireField :=
  { tag := payeeTag, payload := p.bytes }
def expiryField (e : Nat) : WireField :=
  { tag := expiryTag, payload := encodeNat e }
def minFinalCltvField (c : Nat) : WireField :=
  { tag := minFinalCltvTag, payload := encodeNat c }
def featuresField (f : InvoiceFeatures) : WireField :=
  { tag := featuresTag, payload := encodeFeatures f }
def routeHintField (h : RouteHintHop) : WireField :=
  { tag := routeHintTag, payload := encodeHop h }

def parsePaymentHashField (f : WireField) : Option PaymentHash :=
  if f.tag = paymentHashTag ∧ f.payload.size = 32 then some ⟨f.payload⟩ else none
def parsePaymentSecretField (f : WireField) : Option PaymentSecret :=
  if f.tag = paymentSecretTag ∧ f.payload.size = 32 then some ⟨f.payload⟩ else none
def parsePayeeField (f : WireField) : Option PubKey :=
  if f.tag = payeeTag ∧ f.payload.size = 33 then some ⟨f.payload⟩ else none
def parseNatField (f : WireField) (tag : Nat) : Option Nat :=
  if f.tag = tag then decodeNat f.payload else none
def parseFeaturesField (f : WireField) : Option InvoiceFeatures :=
  if f.tag = featuresTag then decodeFeatures f.payload else none
def parseRouteHintField (f : WireField) : Option RouteHintHop :=
  if f.tag = routeHintTag then decodeHop f.payload else none

/-- **Payment-hash field round trip.**  The 32-byte length is the exact
canonicality condition. -/
theorem parsePaymentHashField_print {p : PaymentHash} (hp : p.bytes.size = 32) :
    parsePaymentHashField (paymentHashField p) = some p := by
  cases p with | mk b => simp [parsePaymentHashField, paymentHashField, hp]

/-- **Payment-secret field round trip.** -/
theorem parsePaymentSecretField_print {s : PaymentSecret} (hs : s.bytes.size = 32) :
    parsePaymentSecretField (paymentSecretField s) = some s := by
  cases s with | mk b => simp [parsePaymentSecretField, paymentSecretField, hs]

/-- **Payee-key field round trip.** -/
theorem parsePayeeField_print {p : PubKey} (hp : p.bytes.size = 33) :
    parsePayeeField (payeeField p) = some p := by
  cases p with | mk b => simp [parsePayeeField, payeeField, hp]

/-- **Numeric field round trip.** -/
theorem parseNatField_print {n tag : Nat} (h : n < 2 ^ 64) :
    parseNatField { tag := tag, payload := encodeNat n } tag = some n := by
  have hlt : n < 256 ^ 8 := by rwa [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]
  simp [parseNatField, decodeNat, encodeNat, beBytes_size,
    decodeBE_beBytes_of_lt n 8 hlt]

/-- **Feature field round trip.** -/
theorem parseFeaturesField_print (f : InvoiceFeatures) :
    parseFeaturesField (featuresField f) = some f := by
  simp [parseFeaturesField, featuresField, decodeFeatures_encodeFeatures]

/-- **Route-hint field round trip.** -/
theorem parseRouteHintField_print {h : RouteHintHop} (hh : h.Valid) :
    parseRouteHintField (routeHintField h) = some h := by
  simp [parseRouteHintField, routeHintField, decodeHop_encodeHop hh]

/-! ## 3. Record codec and round trip -/

/-- The fields after the header.  This is the semantic analogue of the BOLT 11
data-part tagged-field list. -/
structure WireFields where
  paymentHash : PaymentHash
  paymentSecret : PaymentSecret
  payee : PubKey
  expiry : Nat
  minFinalCltvExpiry : Nat
  features : InvoiceFeatures
  routeHints : List RouteHintHop
deriving Repr

/-- Canonicality of the tagged-field part. -/
structure WireFields.Canonical (w : WireFields) : Prop where
  paymentHashLength : w.paymentHash.bytes.size = 32
  paymentSecretLength : w.paymentSecret.bytes.size = 32
  payeeLength : w.payee.bytes.size = 33
  expiryBound : w.expiry < 2 ^ 64
  minFinalCltvBound : w.minFinalCltvExpiry < 2 ^ 64
  routeHintsValid : ∀ h ∈ w.routeHints, h.Valid

/-- Print the fixed canonical order `p, s, n, x, c, f, r*`. -/
def printFields (w : WireFields) : List WireField :=
  [paymentHashField w.paymentHash, paymentSecretField w.paymentSecret,
   payeeField w.payee, expiryField w.expiry,
   minFinalCltvField w.minFinalCltvExpiry, featuresField w.features] ++
  w.routeHints.map routeHintField

/-- Parse a sequence of `r` fields into a flat hop list. -/
def parseHints : List WireField → Option (List RouteHintHop)
  | [] => some []
  | f :: fs =>
      match parseRouteHintField f with
      | none => none
      | some h =>
          match parseHints fs with
          | none => none
          | some hs => some (h :: hs)

/-- Parse exactly the canonical fixed order.  Wrong tags, wrong lengths,
missing fields, duplicate fields, and extra non-`r` fields are rejected. -/
def parseFields : List WireField → Option WireFields
  | f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: rest =>
      match parsePaymentHashField f1 with
      | none => none
      | some ph =>
        match parsePaymentSecretField f2 with
        | none => none
        | some ps =>
          match parsePayeeField f3 with
          | none => none
          | some payee =>
            match parseNatField f4 expiryTag with
            | none => none
            | some ex =>
              match parseNatField f5 minFinalCltvTag with
              | none => none
              | some c =>
                match parseFeaturesField f6 with
                | none => none
                | some ft =>
                  match parseHints rest with
                  | none => none
                  | some hs => some ⟨ph, ps, payee, ex, c, ft, hs⟩
  | _ => none

/-- **Hint-list round trip.** -/
theorem parseHints_print (hs : List RouteHintHop)
    (hv : ∀ h ∈ hs, h.Valid) :
    parseHints (hs.map routeHintField) = some hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      have hh : h.Valid := hv h (by simp)
      have hhs : ∀ x ∈ hs, x.Valid := fun x hx => hv x (by simp [hx])
      simp [List.map_cons, parseHints, parseRouteHintField_print hh, ih hhs]

/-- **Field-list round trip.**  For canonical fields, printing and parsing
returns the same field structure.  This is the core serialization theorem. -/
theorem parseFields_printFields (w : WireFields) (hw : w.Canonical) :
    parseFields (printFields w) = some w := by
  rcases w with ⟨ph, ps, payee, ex, c, ft, hints⟩
  rcases hw with ⟨hph, hps, hpay, hex, hc, hhints⟩
  simp [printFields, parseFields, expiryField, minFinalCltvField,
    parsePaymentHashField_print hph, parsePaymentSecretField_print hps,
    parsePayeeField_print hpay, parseNatField_print hex, parseNatField_print hc,
    parseFeaturesField_print, parseHints_print hints hhints]

/-! ### Header and full wire record -/

/-- The pre-bech32 header: HRP token, optional amount, 35-bit timestamp, and
the compact signature. -/
structure WireHeader where
  hrp : String
  amount : Option Msat
  timestamp : Nat
  signature : InvoiceSignature
deriving Repr

/-- A wire record is a header plus the canonical tagged-field list. -/
structure WireRecord where
  header : WireHeader
  fields : List WireField
deriving Repr

/-- The additive wire invoice.  It has every core `Invoice` field except the
description (which is outside this codec and supplied to `toInvoice`) and adds
a flat route-hint list. -/
structure WireInvoice where
  network : Network
  amount : Option Msat
  timestamp : Timestamp
  paymentHash : PaymentHash
  paymentSecret : PaymentSecret
  expiry : Nat
  features : InvoiceFeatures
  routeHints : List RouteHintHop
  payee : PubKey
  signature : InvoiceSignature
  minFinalCltvExpiry : Nat
deriving Repr

def WireInvoice.fieldsOf (w : WireInvoice) : WireFields :=
  { paymentHash := w.paymentHash, paymentSecret := w.paymentSecret,
    payee := w.payee, expiry := w.expiry,
    minFinalCltvExpiry := w.minFinalCltvExpiry, features := w.features,
    routeHints := w.routeHints }

/-- Canonicality of a wire invoice: the header fields fit the modelled widths
and the field structure is canonical. -/
structure WireInvoice.Canonical (w : WireInvoice) : Prop where
  paymentHashLength : w.paymentHash.bytes.size = 32
  paymentSecretLength : w.paymentSecret.bytes.size = 32
  payeeLength : w.payee.bytes.size = 33
  signatureLength : w.signature.bytes.size = 65
  amountBound : ∀ a : Msat, w.amount = some a → a.val ≤ Msat.MAX.val
  timestampBound : w.timestamp ≤ MAX_TIMESTAMP
  expiryBound : w.expiry < 2 ^ 64
  minFinalCltvBound : w.minFinalCltvExpiry < 2 ^ 64
  routeHintsValid : ∀ h ∈ w.routeHints, h.Valid

theorem WireInvoice.fieldsOf_canonical {w : WireInvoice} (hw : w.Canonical) :
    w.fieldsOf.Canonical :=
  ⟨hw.paymentHashLength, hw.paymentSecretLength, hw.payeeLength,
   hw.expiryBound, hw.minFinalCltvBound, hw.routeHintsValid⟩

def printHeader (w : WireInvoice) : WireHeader :=
  { hrp := prefixOf w.network, amount := w.amount,
    timestamp := w.timestamp, signature := w.signature }

def print (w : WireInvoice) : WireRecord :=
  { header := printHeader w, fields := printFields w.fieldsOf }

def parseHeader (h : WireHeader) :
    Option (Network × Option Msat × Nat × InvoiceSignature) :=
  match networkOfPrefix h.hrp with
  | none => none
  | some n => some (n, h.amount, h.timestamp, h.signature)

/-- Canonical parser for the complete record. -/
def parse (r : WireRecord) : Option WireInvoice :=
  match parseHeader r.header with
  | none => none
  | some (n, a, ts, sig) =>
      match parseFields r.fields with
      | none => none
      | some f =>
          some { network := n, amount := a, timestamp := ts,
                 paymentHash := f.paymentHash,
                 paymentSecret := f.paymentSecret, expiry := f.expiry,
                 features := f.features, routeHints := f.routeHints,
                 payee := f.payee, signature := sig,
                 minFinalCltvExpiry := f.minFinalCltvExpiry }

/-- **Header round trip.** -/
theorem parseHeader_printHeader (w : WireInvoice) :
    parseHeader (printHeader w) =
      some (w.network, w.amount, w.timestamp, w.signature) := by
  simp [parseHeader, printHeader, networkOfPrefix_prefixOf]

/-- **Wire-invoice round trip.**  The main serialization theorem: parsing the
canonical printing of a canonical wire invoice returns the invoice itself. -/
theorem parse_print (w : WireInvoice) (hw : w.Canonical) :
    parse (print w) = some w := by
  have hf : w.fieldsOf.Canonical := WireInvoice.fieldsOf_canonical hw
  have hpf : parseFields (printFields w.fieldsOf) = some w.fieldsOf :=
    parseFields_printFields w.fieldsOf hf
  have hpf' : parseFields (printFields
      { paymentHash := w.paymentHash, paymentSecret := w.paymentSecret,
        payee := w.payee, expiry := w.expiry,
        minFinalCltvExpiry := w.minFinalCltvExpiry, features := w.features,
        routeHints := w.routeHints }) = some
      { paymentHash := w.paymentHash, paymentSecret := w.paymentSecret,
        payee := w.payee, expiry := w.expiry,
        minFinalCltvExpiry := w.minFinalCltvExpiry, features := w.features,
        routeHints := w.routeHints } := by
    simpa [WireInvoice.fieldsOf] using hpf
  simp [parse, print, printHeader, parseHeader, networkOfPrefix_prefixOf,
    WireInvoice.fieldsOf, hpf']

/-- **Printing is injective on canonical invoices.** -/
theorem print_injective {a b : WireInvoice} (ha : a.Canonical) (hb : b.Canonical)
    (h : print a = print b) : a = b := by
  have hpa := parse_print a ha
  rw [h, parse_print b hb] at hpa
  exact (Option.some.inj hpa).symm

/-- The parsed payment hash is the printed one. -/
theorem parse_print_paymentHash {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.paymentHash = w.paymentHash := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-- The parsed payment secret is the printed one. -/
theorem parse_print_paymentSecret {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.paymentSecret = w.paymentSecret := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-- The parsed payee key is the printed one. -/
theorem parse_print_payee {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.payee = w.payee := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-- The parsed expiry is the printed one. -/
theorem parse_print_expiry {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.expiry = w.expiry := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-- The parsed feature bits are the printed ones. -/
theorem parse_print_features {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.features = w.features := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-- The parsed route hints are the printed ones. -/
theorem parse_print_routeHints {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') : w'.routeHints = w.routeHints := by
  rw [parse_print w hw] at h
  have hw' : w' = w := (Option.some.inj h).symm
  rw [hw']

/-! ## 4. Projection to the core invoice model -/

/-- Embed a core invoice in the wire model.  Route hints are absent because
the core `Invoice` has no such field. -/
def ofInvoice (i : Invoice) : WireInvoice :=
  { network := i.network, amount := i.amount, timestamp := i.timestamp,
    paymentHash := i.paymentHash, paymentSecret := i.paymentSecret,
    expiry := i.expiry, features := i.features, routeHints := [],
    payee := i.payee, signature := i.signature,
    minFinalCltvExpiry := i.minFinalCltvExpiry }

/-- Project a wire invoice to the core model.  The description is an explicit
argument: the direct-description UTF-8 codec is outside this module. -/
def toInvoice (w : WireInvoice) (d : InvoiceDescription) : Invoice :=
  { network := w.network, amount := w.amount, paymentHash := w.paymentHash,
    timestamp := w.timestamp, expiry := w.expiry, description := d,
    payee := w.payee, features := w.features, signature := w.signature,
    paymentSecret := w.paymentSecret,
    minFinalCltvExpiry := w.minFinalCltvExpiry }

/-- **Core embedding round trip.**  Projecting the embedding of a core
invoice with its own description returns that invoice. -/
theorem toInvoice_ofInvoice (i : Invoice) :
    toInvoice (ofInvoice i) i.description = i := by
  cases i; rfl

/-- The only wire-relevant condition on a description: an `h` digest is 32
bytes.  Direct descriptions are carried out of band. -/
def DescriptionShape : InvoiceDescription → Prop
  | .direct _ => True
  | .hash h => h.size = 32

/-- **Canonical wire projects to valid core invoice.**  Structural validity of
the core invoice follows from wire canonicality plus the description
condition.  No signature check is performed or claimed. -/
theorem toInvoice_valid {w : WireInvoice} (hw : w.Canonical)
    {d : InvoiceDescription} (hd : DescriptionShape d) :
    (toInvoice w d).Valid := by
  rcases w with ⟨net, amt, ts, ph, ps, ex, ft, hints, payee, sig, c⟩
  rcases hw with ⟨hph, hps, hpay, hsig, hamt, hts, hex, hc, hhints⟩
  refine ⟨hph, hps, hpay, hsig, hamt, hts, ?_⟩
  · cases d with
    | direct s => intro h hh; trivial
    | hash b =>
        intro h hh
        have hb : b.size = 32 := by simpa [DescriptionShape] using hd
        injection hh with hbh
        rw [← hbh]
        exact hb

/-- **Core invoice embeds canonically.**  `Invoice.Valid` supplies the fixed
lengths, amount bound, and 35-bit timestamp; the two `Nat` bounds are explicit
because the core model stores expiry/CLTV in unbounded `Nat`. -/
theorem ofInvoice_canonical {i : Invoice} (hi : i.Valid)
    (hex : i.expiry < 2 ^ 64) (hc : i.minFinalCltvExpiry < 2 ^ 64) :
    (ofInvoice i).Canonical := by
  rcases i with ⟨net, amt, ph, ts, ex, desc, payee, ft, sig, ps, c⟩
  rcases hi with ⟨hph, hps, hpay, hsig, hamt, hts, hdesc⟩
  refine ⟨hph, hps, hpay, hsig, hamt, hts, hex, hc, ?_⟩
  · intro h hh
    cases hh

/-- **Wire projection round trip.**  Parsing the printed embedding of a core
invoice returns the embedding. -/
theorem parse_print_ofInvoice {i : Invoice} (hi : i.Valid)
    (hex : i.expiry < 2 ^ 64) (hc : i.minFinalCltvExpiry < 2 ^ 64) :
    parse (print (ofInvoice i)) = some (ofInvoice i) :=
  parse_print _ (ofInvoice_canonical hi hex hc)

/-- Mapping the projection over the parsed embedding gives the core invoice
with the supplied description. -/
theorem toInvoice_parse_print_ofInvoice {i : Invoice} (hi : i.Valid)
    (hex : i.expiry < 2 ^ 64) (hc : i.minFinalCltvExpiry < 2 ^ 64)
    (d : InvoiceDescription) :
    (parse (print (ofInvoice i))).map (fun w => toInvoice w d) =
      some (toInvoice (ofInvoice i) d) := by
  rw [parse_print_ofInvoice hi hex hc]
  rfl


/-! ## 5. Concrete witness and malformed invoices -/

/-- A repeated-byte array, used only to build concrete witnesses. -/
def bytesOf (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (List.replicate n b).toArray

def hashBytes : ByteArray := bytesOf 32 0x11
def secretBytes : ByteArray := bytesOf 32 0x22
def payeeBytes : ByteArray := bytesOf 33 0x02
def sigBytes : ByteArray := bytesOf 65 0x33
def descriptionDigest : ByteArray := bytesOf 32 0x44

theorem hashBytes_size : hashBytes.size = 32 := by decide
theorem secretBytes_size : secretBytes.size = 32 := by decide
theorem payeeBytes_size : payeeBytes.size = 33 := by decide
theorem sigBytes_size : sigBytes.size = 65 := by decide
theorem descriptionDigest_size : descriptionDigest.size = 32 := by decide

/-- A concrete route hint hop: block 800000, tx 3, output 1, 1000 msat base
fee, 100 ppm, 144-block CLTV delta. -/
def witnessHop : RouteHintHop :=
  { channel := { block := 800000, txIndex := 3, outputIndex := 1 }
    feeBaseMsat := 1000
    feeProportionalMillionths := 100
    cltvExpiryDelta := 144 }

theorem witnessHop_valid : witnessHop.Valid := by
  unfold witnessHop RouteHintHop.Valid ShortChannelId.Valid
  decide

/-- A fully populated canonical invoice witness. -/
def witnessWire : WireInvoice :=
  { network := .mainnet
    amount := some (Msat.ofSat 250000)
    timestamp := 1700000000
    paymentHash := ⟨hashBytes⟩
    paymentSecret := ⟨secretBytes⟩
    expiry := 3600
    features := { paymentSecretRequired := true, basicMpp := false,
                  variableLengthOnion := true }
    routeHints := [witnessHop]
    payee := ⟨payeeBytes⟩
    signature := ⟨sigBytes⟩
    minFinalCltvExpiry := 18 }

/-- The concrete witness is canonical. -/
theorem witnessWire_canonical : witnessWire.Canonical := by
  refine ⟨hashBytes_size, secretBytes_size, payeeBytes_size, sigBytes_size,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [witnessWire, Option.some.injEq] at ha
    subst a
    decide
  · decide
  · decide
  · decide
  · intro h hh
    simp only [witnessWire, List.mem_singleton] at hh
    subst h
    exact witnessHop_valid

/-- **Concrete wire witness round trip.** -/
theorem witness_parse : parse (print witnessWire) = some witnessWire :=
  parse_print witnessWire witnessWire_canonical

/-- **Concrete witness projects to a valid core invoice.** -/
theorem witness_toInvoice_valid :
    (toInvoice witnessWire (.hash descriptionDigest)).Valid :=
  toInvoice_valid witnessWire_canonical (by
    simpa [DescriptionShape] using descriptionDigest_size)

/-- The compact signature of the witness is 65 bytes, as BOLT 11 requires. -/
theorem witness_signature_size : witnessWire.signature.bytes.size = 65 :=
  witnessWire_canonical.signatureLength

/-- A 31-byte payment hash, one byte short of BOLT 11's `p` length. -/
def shortHashBytes : ByteArray := bytesOf 31 0x11

theorem shortHashBytes_size : shortHashBytes.size = 31 := by decide

/-- The malformed invoice: the witness with a 31-byte `p` payload. -/
def malformedWire : WireInvoice :=
  { witnessWire with paymentHash := ⟨shortHashBytes⟩ }

theorem malformedWire_not_canonical : ¬ malformedWire.Canonical := by
  intro h
  have hlen : malformedWire.paymentHash.bytes.size = 32 := h.paymentHashLength
  simp [malformedWire, shortHashBytes_size] at hlen

/-- **Malformed invoice is rejected.**  A 31-byte payment hash is printed but
not parsed; the parser's fixed-length check fails closed. -/
theorem malformed_parse_none : parse (print malformedWire) = none := by
  have hsize : (paymentHashField (⟨shortHashBytes⟩ : PaymentHash)).payload.size ≠ 32 := by
    simp [paymentHashField, shortHashBytes_size]
  simp [parse, print, printHeader, parseHeader, networkOfPrefix_prefixOf,
    malformedWire, witnessWire, WireInvoice.fieldsOf, printFields, parseFields,
    parsePaymentHashField, hsize]

theorem parseRouteHintField_paymentHashField (p : PaymentHash) :
    parseRouteHintField (paymentHashField p) = none := by
  simp [parseRouteHintField, paymentHashField, paymentHashTag, routeHintTag]

theorem parseHints_two_bad {f : WireField} {h : RouteHintHop} {g : WireField}
    (hf : parseRouteHintField f = some h)
    (hg : parseRouteHintField g = none) : parseHints (f :: g :: []) = none := by
  simp [parseHints, hf, hg]

/-- A record that appends a duplicate `p` field after the canonical fields. -/
def duplicateHashRecord : WireRecord :=
  { header := (print witnessWire).header
    fields := (print witnessWire).fields ++
      [paymentHashField witnessWire.paymentHash] }

/-- **Duplicate `p` field is rejected.**  The duplicate is not a route hint and
is therefore not absorbed by the canonical `r*` tail. -/
theorem duplicateHash_parse_none : parse duplicateHashRecord = none := by
  have hph : parsePaymentHashField
      (paymentHashField (⟨hashBytes⟩ : PaymentHash)) =
      some (⟨hashBytes⟩ : PaymentHash) :=
    parsePaymentHashField_print hashBytes_size
  have hps : parsePaymentSecretField
      (paymentSecretField (⟨secretBytes⟩ : PaymentSecret)) =
      some (⟨secretBytes⟩ : PaymentSecret) :=
    parsePaymentSecretField_print secretBytes_size
  have hpay : parsePayeeField (payeeField (⟨payeeBytes⟩ : PubKey)) =
      some (⟨payeeBytes⟩ : PubKey) :=
    parsePayeeField_print payeeBytes_size
  have hfeat : parseFeaturesField (featuresField
      { paymentSecretRequired := true, basicMpp := false,
        variableLengthOnion := true }) =
      some { paymentSecretRequired := true, basicMpp := false,
             variableLengthOnion := true } :=
    parseFeaturesField_print _
  have hex : parseNatField (expiryField 3600) expiryTag = some 3600 := by
    simpa [expiryField] using
      (parseNatField_print (n := 3600) (tag := expiryTag) (by decide))
  have hcltv : parseNatField (minFinalCltvField 18) minFinalCltvTag = some 18 := by
    simpa [minFinalCltvField] using
      (parseNatField_print (n := 18) (tag := minFinalCltvTag) (by decide))
  have hbad : parseHints [routeHintField witnessHop,
      paymentHashField (⟨hashBytes⟩ : PaymentHash)] = none :=
    parseHints_two_bad (parseRouteHintField_print witnessHop_valid)
      (parseRouteHintField_paymentHashField _)
  simp [duplicateHashRecord, parse, print, printHeader, parseHeader,
    networkOfPrefix_prefixOf, witnessWire, WireInvoice.fieldsOf, printFields,
    parseFields, hph, hps, hpay, hfeat, hex, hcltv, hbad]

/-! ## 6. Payment-secret and payment-hash binding -/

/-- The raw hash-image relation: `p` commits to `h` when the supplied hash
function maps `p` to `h`.  The hash function is a parameter (C1); nothing here
asserts a concrete SHA-256. -/
def Commits (hash : Preimage → PaymentHash) (p : Preimage)
    (h : PaymentHash) : Prop :=
  hash p = h

/-- The invoice-specific commitment relation. -/
def InvoiceCommits (hash : Preimage → PaymentHash) (p : Preimage)
    (i : Invoice) : Prop :=
  hash p = i.paymentHash

/-- **The exact hash-image boundary.**  A preimage commits to an invoice
exactly when its hash equals the invoice's `p` field.  This is an equality, not
a cryptographic soundness claim. -/
theorem invoiceCommits_iff {hash : Preimage → PaymentHash} {p : Preimage}
    {i : Invoice} :
    InvoiceCommits hash p i ↔ hash p = i.paymentHash :=
  Iff.rfl

/-- **A preimage determines its hash.**  Two invoices that accept the same
preimage carry the same payment hash, with no cryptographic hypothesis. -/
theorem preimage_determines_hash {hash : Preimage → PaymentHash} {p : Preimage}
    {i j : Invoice} (hi : InvoiceCommits hash p i)
    (hj : InvoiceCommits hash p j) : i.paymentHash = j.paymentHash := by
  rw [← hi, ← hj]

/-- **Preimage uniqueness is conditional on injectivity.**  If the hash
function is injective, an invoice's payment hash has at most one committing
preimage. -/
theorem preimage_unique_of_injective {hash : Preimage → PaymentHash}
    (hinj : Function.Injective hash) {i : Invoice} {p q : Preimage}
    (hp : InvoiceCommits hash p i) (hq : InvoiceCommits hash q i) : p = q :=
  hinj (hp.trans hq.symm)

/-- **No preimage means the hash is outside the image.** -/
theorem no_preimage_iff_not_in_image {hash : Preimage → PaymentHash}
    {h : PaymentHash} :
    (¬ ∃ p : Preimage, Commits hash p h) ↔ ∀ p : Preimage, hash p ≠ h := by
  simp [Commits, not_exists]

/-- Payment-secret equality is exactly byte equality: the secret is a
one-field wrapper in the model. -/
theorem paymentSecret_eq_iff_bytes (s t : PaymentSecret) :
    s = t ↔ s.bytes = t.bytes := by
  constructor
  · intro h; rw [h]
  · intro h; cases s; cases t; simpa using h

/-- Payment-hash equality is exactly byte equality. -/
theorem paymentHash_eq_iff_bytes (h k : PaymentHash) :
    h = k ↔ h.bytes = k.bytes := by
  constructor
  · intro hh; rw [hh]
  · intro hh; cases h; cases k; simpa using hh

/-- **Secret binding survives the wire codec.**  Any invoice parsed from the
printed record carries the printed secret. -/
theorem wire_paymentSecret_binding {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') :
    w'.paymentSecret = w.paymentSecret :=
  parse_print_paymentSecret hw h

/-- **Hash binding survives the wire codec.** -/
theorem wire_paymentHash_binding {w w' : WireInvoice} (hw : w.Canonical)
    (h : parse (print w) = some w') :
    w'.paymentHash = w.paymentHash :=
  parse_print_paymentHash hw h

/-! ### Exact hash-image counterexamples -/

def zeroBytes : ByteArray := bytesOf 32 0x00
def oneBytes : ByteArray := bytesOf 32 0x01

def zeroPaymentHash : PaymentHash := ⟨zeroBytes⟩
def onePaymentHash : PaymentHash := ⟨oneBytes⟩

theorem zeroPaymentHash_ne_one : zeroPaymentHash ≠ onePaymentHash := by
  decide

/-- The constant-zero hash function.  It is a legitimate function
`Preimage → PaymentHash`; it is simply not injective. -/
def constantZeroHash (_ : Preimage) : PaymentHash := zeroPaymentHash

theorem zeroBytes_ne_oneBytes : zeroBytes ≠ oneBytes := by
  decide

/-- **Constant hash is not injective.**  The algebraic hash relation alone
does not pin down the preimage. -/
theorem constantZeroHash_not_injective :
    ¬ Function.Injective constantZeroHash := by
  intro hinj
  have hpre : (⟨zeroBytes⟩ : Preimage) = ⟨oneBytes⟩ := hinj rfl
  exact zeroBytes_ne_oneBytes (congrArg Preimage.bytes hpre)

/-- **Collision witness.**  Two distinct preimages commit to the same hash
image, so uniqueness fails without an injectivity hypothesis. -/
theorem constantZeroHash_collision :
    ∃ p q : Preimage, p ≠ q ∧
      Commits constantZeroHash p zeroPaymentHash ∧
      Commits constantZeroHash q zeroPaymentHash := by
  refine ⟨⟨zeroBytes⟩, ⟨oneBytes⟩, ?_, rfl, rfl⟩
  intro h
  exact zeroBytes_ne_oneBytes (congrArg Preimage.bytes h)

/-- A 31-byte preimage is not structurally valid, yet the hash relation still
accepts it: the commitment is an image statement, not a length check. -/
def shortPreimage : Preimage := ⟨shortHashBytes⟩

theorem shortPreimage_not_valid : ¬ shortPreimage.Valid := by
  simp [shortPreimage, Preimage.Valid, shortHashBytes_size]

/-- **Commitment does not imply preimage validity.**  This is the exact
boundary between the algebraic hash image and a canonical 32-byte payment
preimage. -/
theorem commitment_not_valid_preimage :
    ∃ (hash : Preimage → PaymentHash) (p : Preimage) (h : PaymentHash),
      Commits hash p h ∧ ¬ p.Valid :=
  ⟨constantZeroHash, shortPreimage, zeroPaymentHash, rfl, shortPreimage_not_valid⟩

/-! ### Signature acceptance is not proof of payment -/

/-- A concrete invoice whose payment hash is **outside** the image of
`constantZeroHash`.  Every structural field is canonical. -/
def signatureOnlyInvoice : Invoice :=
  { network := .mainnet
    amount := some (Msat.ofSat 1000)
    paymentHash := onePaymentHash
    timestamp := 1700000000
    expiry := 3600
    description := .hash descriptionDigest
    payee := ⟨payeeBytes⟩
    features := { paymentSecretRequired := true, basicMpp := false,
                  variableLengthOnion := true }
    signature := ⟨sigBytes⟩
    paymentSecret := ⟨secretBytes⟩
    minFinalCltvExpiry := 18 }

theorem signatureOnlyInvoice_valid : signatureOnlyInvoice.Valid := by
  refine ⟨hashBytes_size, secretBytes_size, payeeBytes_size, sigBytes_size,
    ?_, ?_, ?_⟩
  · intro a ha
    simp only [signatureOnlyInvoice, Option.some.injEq] at ha
    subst a
    decide
  · decide
  · intro h hh
    simp only [signatureOnlyInvoice, InvoiceDescription.hash.injEq] at hh
    subst h
    exact descriptionDigest_size

/-- The always-accepting checker accepts the concrete invoice. -/
theorem signatureOnly_verifies :
    Invoice.verify (fun _ => ByteArray.empty)
      (fun _ _ _ => true) signatureOnlyInvoice :=
  ⟨signatureOnlyInvoice_valid, rfl⟩

/-- **No preimage commits to the signature-only invoice.**  The invoice's
payment hash is `0x01…`, while `constantZeroHash` always returns `0x00…`. -/
theorem signatureOnly_no_preimage :
    ¬ ∃ p : Preimage, InvoiceCommits constantZeroHash p signatureOnlyInvoice := by
  rintro ⟨p, hp⟩
  have hz : constantZeroHash p = zeroPaymentHash := rfl
  have h : zeroPaymentHash = onePaymentHash := by
    rw [← hz]
    exact hp
  exact zeroPaymentHash_ne_one h

/-- **Signature acceptance is not proof of payment.**  There is a verified
invoice (structural validity plus an accepting checker) for which no preimage
commits to the payment hash.  No cryptographic unforgeability property is
used or claimed: the checker is an explicit always-accepting parameter, and
the counterexample is about the *model's* verification predicate. -/
theorem signature_not_payment :
    ∃ (digest : Invoice → ByteArray)
      (sigCheck : PubKey → ByteArray → InvoiceSignature → Bool)
      (i : Invoice),
      Invoice.verify digest sigCheck i ∧
        ¬ ∃ p : Preimage, InvoiceCommits constantZeroHash p i :=
  ⟨fun _ => ByteArray.empty, fun _ _ _ => true, signatureOnlyInvoice,
   signatureOnly_verifies, signatureOnly_no_preimage⟩

/-- **Signature-only invoice has no payment evidence even for the witness
checker.**  The statement is independent of any particular signature scheme;
it is the separation of `Invoice.verify` from `InvoiceCommits`. -/
theorem signature_only_separates_verify_from_payment :
    Invoice.verify (fun _ => ByteArray.empty) (fun _ _ _ => true)
        signatureOnlyInvoice ∧
      ¬ ∃ p : Preimage, InvoiceCommits constantZeroHash p signatureOnlyInvoice :=
  ⟨signatureOnly_verifies, signatureOnly_no_preimage⟩

end LnLean.Proofs.Payment.InvoiceWireTargets
