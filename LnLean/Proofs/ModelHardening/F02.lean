import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Proofs.Bitcoin.FundingProps

/-!
# F02 — Funding key parser safety

The funding witness script pushes each compressed funding key with
`pushData`.  `pushData` writes `k.size.toUInt8` as the length byte and then
the key bytes.  That is a *direct* `OP_PUSHBYTES_n` only when `1 ≤ k.size ≤ 75`;
for sizes such as 79 (`0x4f`, `OP_1NEGATE`) and 81 (`0x51`, `OP_1`) the
length byte is itself an opcode, so the parser leaves the push encoding and
walks into the key bytes.  This module names the 33-byte invariant, proves
that it makes both key pushes parse verbatim and makes the 2-of-2 script reach
the (unmodelled) `OP_CHECKMULTISIG`, and mechanizes the 79- and 81-byte
counterexamples from `FundingProps`.
-/

-- OBLIGATION: LN-WF-F02

namespace LnLean.Proofs.ModelHardening.F02

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean
open LnLean.Bitcoin
open Bitcoin.Data

/-! ## The 33-byte parser-safety invariant -/

/-- A funding key is *parser safe* when it is exactly one compressed
secp256k1 key: 33 bytes.  Equivalently, `pushData` emits the direct push
opcode `0x21` followed by the key, with no opcode collision. -/
def FundingKeyParseSafe (k : PubKey) : Prop := k.bytes.size = 33

/-- Both funding keys of a channel are parser safe.  This is the reusable
invariant missing from the unconditional `witnessScript_parse_eq_none`
statement. -/
def FundingKeysParseSafe (p : FundingParams) : Prop :=
  FundingKeyParseSafe p.localFundingKey ∧
  FundingKeyParseSafe p.remoteFundingKey

theorem fundingKeyParseSafe_iff_valid (k : PubKey) :
    FundingKeyParseSafe k ↔ k.Valid := Iff.rfl

theorem fundingKeysParseSafe_of_wellFormed (p : FundingParams)
    (h : p.WellFormed) : FundingKeysParseSafe p := by
  rcases h with ⟨-, -, h1, h2, -, -⟩
  exact ⟨h1, h2⟩

/-- The direct-push encoding of a safe funding key: the length byte is
`0x21`, the BIP 62 direct-push opcode for 33 bytes. -/
theorem pushData_fundingKey_parseSafe (k : PubKey)
    (h : FundingKeyParseSafe k) :
    pushData k.bytes = (ByteArray.empty.push 0x21) ++ k.bytes := by
  simp [pushData, FundingKeyParseSafe] at h ⊢
  rw [h]
  rfl

/-! ## Parser lemmas: a 33-byte push decodes verbatim

These are local copies of the (private) byte lemmas in
`LnLean.Proofs.Bitcoin.FundingProps`, generalised to our invariant. -/

private theorem getElem?_append_lt (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]? = a[i]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append, ite_eq_left (by simpa using h)]
  rw [show a[i]? = a.data[i]? from rfl]

private theorem getElem?_append_ge (a b : ByteArray) (i : Nat) (h : a.size ≤ i) :
    (a ++ b)[i]? = b[i - a.size]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append, ite_eq_right (by simpa using h)]
  rw [show b[i - a.size]? = b.data[i - a.size]? from rfl]
  rfl

private theorem getElem?_push_eq (a : ByteArray) (x : UInt8) :
    (a.push x)[a.size]? = some x := by
  rw [show (a.push x)[a.size]? = (a.push x).data[a.size]? from rfl,
      ByteArray.data_push, Array.getElem?_push,
      ite_eq_left (show a.size = a.data.size from rfl)]

private theorem getElem?_pushData_len (pre k rest : ByteArray) :
    (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k) ++ rest)[pre.size]?
      = some k.size.toUInt8 := by
  rw [getElem?_append_lt (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k)) rest pre.size
    (by simp only [ByteArray.size_append, ByteArray.size_push]; omega)]
  rw [getElem?_append_ge pre (ByteArray.empty.push k.size.toUInt8 ++ k) pre.size (by omega)]
  simp only [Nat.sub_self]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  rw [getElem?_append_lt (ByteArray.empty.push k.size.toUInt8) k ByteArray.empty.size
    (by simp only [ByteArray.size_push, ByteArray.size_empty]; omega)]
  exact getElem?_push_eq _ _

private theorem foldl_range_get_eq_extract (b : ByteArray) (i n : Nat)
    (h : i + n ≤ b.size) :
    (List.range n).foldl (fun acc k => acc.push (b.get! (i + k))) ByteArray.empty
      = b.extract i (i + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    have hlt : i + n < b.size := by omega
    have hget : b.get! (i + n) = b[i + n] := by
      show b.data[i + n]! = b[i + n]
      rw [getElem!_pos b.data (i + n) (by simpa using hlt)]
      rfl
    rw [hget]
    rw [← ByteArray.append_toByteArray_singleton]
    have hone : b.extract (i + n) (i + n + 1) = [b[i + n]].toByteArray :=
      ByteArray.extract_add_one (by omega)
    rw [← hone]
    have hsplit : b.extract (min i (i + n)) (max (i + n) (i + n + 1)) =
        b.extract i (i + n) ++ b.extract (i + n) (i + n + 1) :=
      ByteArray.extract_append_extract.symm
    rw [show min i (i + n) = i from Nat.min_eq_left (by omega),
        show max (i + n) (i + n + 1) = i + n + 1 from Nat.max_eq_right (by omega)] at hsplit
    rw [show i + (n + 1) = i + n + 1 from by omega]
    exact hsplit.symm

private theorem takeBytes_eq_extract (b : ByteArray) (i n : Nat)
    (h : i + n ≤ b.size) :
    Bitcoin.Data.takeBytes b i n = some (b.extract i (i + n)) := by
  unfold Bitcoin.Data.takeBytes
  rw [ite_eq_left h, foldl_range_get_eq_extract b i n h]

private theorem extract_push33 (pre k rest : ByteArray) (hk : k.size = 33) :
    (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k) ++ rest).extract
        (pre.size + 1) (pre.size + 34) = k := by
  rw [ByteArray.extract_append]
  have hrest : rest.extract
      ((pre.size + 1) - (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k)).size)
      ((pre.size + 34) - (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k)).size)
      = ByteArray.empty := by
    rw [ByteArray.extract_eq_empty_iff]
    simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, hk]
    omega
  rw [hrest, ByteArray.append_empty]
  rw [ByteArray.extract_append_size_add]
  rw [show (1 : Nat) = (ByteArray.empty.push k.size.toUInt8).size + 0 from by simp]
  rw [show (34 : Nat) = (ByteArray.empty.push k.size.toUInt8).size + k.size from by simp [hk]]
  rw [ByteArray.extract_append_size_add]
  rw [ByteArray.extract_zero_size]

/-- A 33-byte `pushData` is decoded by the wave-A parser as exactly one
`.push` of the key bytes, consuming 34 bytes.  This is the positive half of
parser safety. -/
theorem decodeOp_pushData33 (pre k rest : ByteArray) (hk : k.size = 33) :
    Bitcoin.Data.decodeOp (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k) ++ rest) pre.size
      = some (.push k, pre.size + 34) := by
  unfold Bitcoin.Data.decodeOp
  rw [getElem?_pushData_len pre k rest]
  have hn : k.size.toUInt8.toNat = 33 := by simp [hk]
  simp only [hn]
  rw [ite_eq_right (by decide : ¬ (33 : Nat) = 0)]
  rw [ite_eq_left (by decide : (33 : Nat) ≤ 75)]
  rw [takeBytes_eq_extract]
  · rw [extract_push33 pre k rest hk]
  · simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty]
    omega

/-- `0x21` is a direct-push opcode, not one of the opcodes that `decodeOp`
recognizes.  This is the byte-level reason a 33-byte key cannot be mistaken
for an instruction. -/
theorem pushData_fundingKey_prefix_not_opcode (k : PubKey)
    (h : FundingKeyParseSafe k) :
    (pushData k.bytes)[0]? = some 0x21 ∧
    0 < 0x21 ∧ 0x21 ≤ 0x4b := by
  have hsize : k.bytes.size = 33 := h
  refine ⟨?_, by decide, by decide⟩
  rw [pushData_fundingKey_parseSafe k h]
  rw [getElem?_append_lt (ByteArray.empty.push 0x21) k.bytes 0 (by simp)]
  exact getElem?_push_eq _ _

/-- Both key pushes of a parser-safe funding script decode verbatim at their
BOLT 3 offsets: the first at index 1, the second at index 35. -/
theorem fundingScript_key_pushes_decode (p : FundingParams)
    (h : FundingKeysParseSafe p) :
    let keys := orderedFundingKeys p.localFundingKey p.remoteFundingKey
    Bitcoin.Data.decodeOp p.witnessScript.bytes 1 = some (.push keys.1.bytes, 35) ∧
    Bitcoin.Data.decodeOp p.witnessScript.bytes 35 = some (.push keys.2.bytes, 69) := by
  rcases h with ⟨h1, h2⟩
  simp only [FundingKeyParseSafe] at h1 h2
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair p.localFundingKey p.remoteFundingKey with hord | hord
  · have hscript : p.witnessScript.bytes =
        ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG := by
      simp [FundingParams.witnessScript, pushData, hord, ByteArray.append_assoc]
    rw [hscript]
    have e1 : Bitcoin.Data.decodeOp
        (ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG) 1
        = some (.push p.localFundingKey.bytes, 35) := by
      simpa [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        ByteArray.append_assoc, h1, h2] using decodeOp_pushData33 (ByteArray.empty.push 0x52)
          p.localFundingKey.bytes
          ((ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
            ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) h1
    have e2 : Bitcoin.Data.decodeOp
        (ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG) 35
        = some (.push p.remoteFundingKey.bytes, 69) := by
      simpa [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        ByteArray.append_assoc, h1, h2] using decodeOp_pushData33
          (ByteArray.empty.push 0x52
            ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
                ++ p.localFundingKey.bytes))
          p.remoteFundingKey.bytes
          (ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) h2
    exact ⟨by simpa [hord] using e1, by simpa [hord] using e2⟩
  · have hscript : p.witnessScript.bytes =
        ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG := by
      simp [FundingParams.witnessScript, pushData, hord, ByteArray.append_assoc]
    rw [hscript]
    have e1 : Bitcoin.Data.decodeOp
        (ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG) 1
        = some (.push p.remoteFundingKey.bytes, 35) := by
      simpa [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        ByteArray.append_assoc, h1, h2] using decodeOp_pushData33 (ByteArray.empty.push 0x52)
          p.remoteFundingKey.bytes
          ((ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
            ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) h2
    have e2 : Bitcoin.Data.decodeOp
        (ByteArray.empty.push 0x52
          ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
              ++ p.remoteFundingKey.bytes)
          ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8
              ++ p.localFundingKey.bytes)
          ++ ByteArray.empty.push 0x52
          ++ ByteArray.empty.push OP_CHECKMULTISIG) 35
        = some (.push p.localFundingKey.bytes, 69) := by
      simpa [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
        ByteArray.append_assoc, h1, h2] using decodeOp_pushData33
          (ByteArray.empty.push 0x52
            ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8
                ++ p.remoteFundingKey.bytes))
          p.localFundingKey.bytes
          (ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) h1
    exact ⟨by simpa [hord] using e1, by simpa [hord] using e2⟩

/-! ## The corrected witness-script parse theorem -/

private theorem decodeOp_const2_at (pre rest : ByteArray) :
    Bitcoin.Data.decodeOp (pre ++ ByteArray.empty.push 0x52 ++ rest) pre.size
      = some (.const 2, pre.size + 1) := by
  have hbyte : (pre ++ ByteArray.empty.push 0x52 ++ rest)[pre.size]? = some (0x52 : UInt8) := by
    rw [getElem?_append_lt (pre ++ ByteArray.empty.push 0x52) rest pre.size
      (by simp only [ByteArray.size_append, ByteArray.size_push]; omega)]
    rw [getElem?_append_ge pre (ByteArray.empty.push 0x52) pre.size (by omega)]
    rw [show pre.size - pre.size = 0 from by omega]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl]
    exact getElem?_push_eq _ _
  unfold Bitcoin.Data.decodeOp
  rw [hbyte]
  simp

private theorem getElem?_checkMultisig (pre : ByteArray) :
    (pre ++ ByteArray.empty.push OP_CHECKMULTISIG)[pre.size]? = some OP_CHECKMULTISIG := by
  rw [getElem?_append_ge pre (ByteArray.empty.push OP_CHECKMULTISIG) pre.size (by omega)]
  rw [show pre.size - pre.size = 0 from by omega]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  exact getElem?_push_eq _ _

private theorem parseWith_step (b : ByteArray) (i i' fuel : Nat)
    (acc : List Bitcoin.Data.ScriptInstr) (op : Bitcoin.Data.ScriptInstr)
    (hi : i < b.size) (hdec : Bitcoin.Data.decodeOp b i = some (op, i')) :
    Bitcoin.Data.Script.parse.parseWith b (fuel + 1) i acc
      = Bitcoin.Data.Script.parse.parseWith b fuel i' (op :: acc) := by
  have hni : ¬ b.size ≤ i := by omega
  simp [Bitcoin.Data.Script.parse.parseWith, hni, hdec]

private theorem parseWith_checkMultisig (b : ByteArray) (i fuel : Nat)
    (acc : List Bitcoin.Data.ScriptInstr)
    (h : b[i]? = some OP_CHECKMULTISIG) :
    Bitcoin.Data.Script.parse.parseWith b (fuel + 1) i acc = none := by
  have hi : i < b.size := by
    rcases Nat.lt_or_ge i b.size with h' | h'
    · exact h'
    · have hnone : b[i]? = none := by simp [h']
      rw [h] at hnone
      simp at hnone
  have hb : b[i] = OP_CHECKMULTISIG := by
    have h' := h
    simp [hi] at h'
    exact h'
  have hn : OP_CHECKMULTISIG.toNat = 174 := by rfl
  simp [Bitcoin.Data.Script.parse.parseWith, Bitcoin.Data.decodeOp, hi, hb, hn]

private theorem parseWith_witnessScript (k1 k2 : ByteArray)
    (hk1 : k1.size = 33) (hk2 : k2.size = 33) :
    Bitcoin.Data.Script.parse.parseWith
      (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push k1.size.toUInt8 ++ k1)
        ++ (ByteArray.empty.push k2.size.toUInt8 ++ k2)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG) 71 0 [] = none := by
  let B : ByteArray :=
    ByteArray.empty.push 0x52
      ++ (ByteArray.empty.push k1.size.toUInt8 ++ k1)
      ++ (ByteArray.empty.push k2.size.toUInt8 ++ k2)
      ++ ByteArray.empty.push 0x52
      ++ ByteArray.empty.push OP_CHECKMULTISIG
  change Bitcoin.Data.Script.parse.parseWith B 71 0 [] = none
  have d0 : Bitcoin.Data.decodeOp B 0 = some (.const 2, 1) := by
    simpa [B, ByteArray.append_assoc] using decodeOp_const2_at ByteArray.empty
      ((ByteArray.empty.push k1.size.toUInt8 ++ k1)
        ++ (ByteArray.empty.push k2.size.toUInt8 ++ k2)
        ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG)
  have d1 : Bitcoin.Data.decodeOp B 1 = some (.push k1, 35) := by
    simpa [B, ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_push,
      ByteArray.size_empty]
      using decodeOp_pushData33 (ByteArray.empty.push 0x52) k1
        ((ByteArray.empty.push k2.size.toUInt8 ++ k2)
          ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) hk1
  have d2 : Bitcoin.Data.decodeOp B 35 = some (.push k2, 69) := by
    simpa [B, ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_push,
      ByteArray.size_empty, hk1]
      using decodeOp_pushData33
        (ByteArray.empty.push 0x52 ++ (ByteArray.empty.push k1.size.toUInt8 ++ k1)) k2
        (ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG) hk2
  have d3 : Bitcoin.Data.decodeOp B 69 = some (.const 2, 70) := by
    simpa [B, ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_push,
      ByteArray.size_empty, hk1, hk2]
      using decodeOp_const2_at
        (ByteArray.empty.push 0x52 ++ (ByteArray.empty.push k1.size.toUInt8 ++ k1)
          ++ (ByteArray.empty.push k2.size.toUInt8 ++ k2))
        (ByteArray.empty.push OP_CHECKMULTISIG)
  rw [parseWith_step B 0 1 70 [] (.const 2) (by simp [B, hk1, hk2]) d0]
  rw [parseWith_step B 1 35 69 [.const 2] (.push k1) (by simp [B, hk1, hk2]) d1]
  rw [parseWith_step B 35 69 68 [.push k1, .const 2] (.push k2)
    (by simp [B, hk1, hk2]) d2]
  rw [parseWith_step B 69 70 67 [.push k2, .push k1, .const 2] (.const 2)
    (by simp [B, hk1, hk2]) d3]
  apply parseWith_checkMultisig B 70 66 [.const 2, .push k2, .push k1, .const 2]
  simpa [B, ByteArray.append_assoc, ByteArray.size_append, ByteArray.size_push,
    ByteArray.size_empty, hk1, hk2]
    using getElem?_checkMultisig
      (ByteArray.empty.push 0x52 ++ (ByteArray.empty.push k1.size.toUInt8 ++ k1)
        ++ (ByteArray.empty.push k2.size.toUInt8 ++ k2) ++ ByteArray.empty.push 0x52)

/-- **Corrected witness-script parse theorem.**  If both funding keys satisfy
the 33-byte parser-safety invariant, then the BOLT 3 witness script parses to
the two key pushes and the two `OP_2` constants, and stops at the trailing
`OP_CHECKMULTISIG` (which the wave-A `ScriptInstr` cannot represent).  In
particular the parser never reinterprets key bytes as opcodes. -/
theorem waveF_f02_witnessScript_parse_eq_none_of_parseSafe
    (p : FundingParams) (h : FundingKeysParseSafe p) :
    p.witnessScript.parse = none := by
  rcases h with ⟨h1, h2⟩
  simp only [FundingKeyParseSafe] at h1 h2
  rcases LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_pair p.localFundingKey p.remoteFundingKey with hord | hord
  · simp only [FundingParams.witnessScript, pushData, hord]
    change Bitcoin.Data.Script.parse.parseWith
      (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG)
      (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG).size 0 [] = none
    rw [show (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG).size = 71 from by
      simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, h1, h2]]
    exact parseWith_witnessScript p.localFundingKey.bytes p.remoteFundingKey.bytes h1 h2
  · simp only [FundingParams.witnessScript, pushData, hord]
    change Bitcoin.Data.Script.parse.parseWith
      (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG)
      (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG).size 0 [] = none
    rw [show (ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push p.remoteFundingKey.bytes.size.toUInt8 ++ p.remoteFundingKey.bytes)
        ++ (ByteArray.empty.push p.localFundingKey.bytes.size.toUInt8 ++ p.localFundingKey.bytes)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG).size = 71 from by
      simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, h1, h2]]
    exact parseWith_witnessScript p.remoteFundingKey.bytes p.localFundingKey.bytes h2 h1

/-! ## Counterexamples: 79- and 81-byte keys are not parser safe -/

/-- Key whose length byte `79 = 0x4f` is `OP_1NEGATE`.  Body offsets 0, 72 and
76 are chosen so that successive pushes walk over the second key and consume
the trailing `OP_2 OP_CHECKMULTISIG`. -/
private def cexKey79 : ByteArray :=
  ([0x4b] ++ List.replicate 71 (0x00 : UInt8) ++ [0x08]
    ++ List.replicate 3 (0x00 : UInt8) ++ [0x4b]
    ++ List.replicate 2 (0x00 : UInt8)).toByteArray

/-- Key whose length byte `81 = 0x51` is `OP_1`. -/
private def cexKey81 : ByteArray :=
  ([0x4b] ++ List.replicate 69 (0x00 : UInt8) ++ [0x0c]
    ++ List.replicate 5 (0x00 : UInt8) ++ [0x4b]
    ++ List.replicate 4 (0x00 : UInt8)).toByteArray

private def cexParams (k : ByteArray) : FundingParams :=
  { fundingSatoshis := 0
    pushMsat := ⟨0⟩
    localFundingKey := ⟨k⟩
    remoteFundingKey := ⟨k⟩
    witnessScriptHash := ByteArray.empty
    temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }

private theorem cexParams_witnessScript (k : ByteArray) :
    (cexParams k).witnessScript.bytes =
      ByteArray.empty.push 0x52
        ++ (ByteArray.empty.push k.size.toUInt8 ++ k)
        ++ (ByteArray.empty.push k.size.toUInt8 ++ k)
        ++ ByteArray.empty.push 0x52
        ++ ByteArray.empty.push OP_CHECKMULTISIG := by
  simp [FundingParams.witnessScript, cexParams, pushData, ByteArray.append_assoc]
  rw [LnLean.Proofs.Bitcoin.FundingProps.orderedFundingKeys_self]

set_option maxRecDepth 10000 in
/-- The witness script built from two 79-byte keys parses successfully: the
length byte `0x4f` is decoded as `OP_1NEGATE`, the key body is followed as
opcodes, and the final push swallows `OP_2 OP_CHECKMULTISIG`. -/
theorem waveF_f02_cex79 :
    ∃ p : FundingParams,
      p.localFundingKey.bytes.size = 79 ∧
      p.remoteFundingKey.bytes.size = 79 ∧
      ¬ FundingKeyParseSafe p.localFundingKey ∧
      p.witnessScript.parse ≠ none := by
  refine ⟨cexParams cexKey79, by decide, by decide, by (show ¬ cexKey79.size = 33; decide), ?_⟩
  let B : ByteArray := ByteArray.empty.push 0x52
    ++ (ByteArray.empty.push cexKey79.size.toUInt8 ++ cexKey79)
    ++ (ByteArray.empty.push cexKey79.size.toUInt8 ++ cexKey79)
    ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG
  have hbytes : (cexParams cexKey79).witnessScript.bytes = B := by
    simpa [B] using cexParams_witnessScript cexKey79
  have hsize : B.size = 163 := by decide
  have d0 : Bitcoin.Data.decodeOp B 0 = some (.const 2, 1) := by decide
  have d1 : Bitcoin.Data.decodeOp B 1 = some (.op1negate, 2) := by decide
  have d2 : Bitcoin.Data.decodeOp B 2 = some (.push (B.extract 3 78), 78) := by decide
  have d3 : Bitcoin.Data.decodeOp B 78 = some (.push (B.extract 79 154), 154) := by decide
  have d4 : Bitcoin.Data.decodeOp B 154 = some (.push (B.extract 155 163), 163) := by decide
  unfold Bitcoin.Data.Script.parse
  rw [hbytes, hsize]
  rw [parseWith_step B 0 1 162 [] (.const 2) (by rw [hsize]; omega) d0]
  rw [parseWith_step B 1 2 161 [.const 2] (.op1negate) (by rw [hsize]; omega) d1]
  rw [parseWith_step B 2 78 160 [.op1negate, .const 2]
    (.push (B.extract 3 78)) (by rw [hsize]; omega) d2]
  rw [parseWith_step B 78 154 159
    [.push (B.extract 3 78), .op1negate, .const 2]
    (.push (B.extract 79 154)) (by rw [hsize]; omega) d3]
  rw [parseWith_step B 154 163 158
    [.push (B.extract 79 154), .push (B.extract 3 78), .op1negate, .const 2]
    (.push (B.extract 155 163)) (by rw [hsize]; omega) d4]
  simp [Bitcoin.Data.Script.parse.parseWith, hsize]

set_option maxRecDepth 10000 in
/-- The 81-byte counterpart: `0x51` is `OP_1`. -/
theorem waveF_f02_cex81 :
    ∃ p : FundingParams,
      p.localFundingKey.bytes.size = 81 ∧
      p.remoteFundingKey.bytes.size = 81 ∧
      ¬ FundingKeyParseSafe p.localFundingKey ∧
      p.witnessScript.parse ≠ none := by
  refine ⟨cexParams cexKey81, by decide, by decide, by (show ¬ cexKey81.size = 33; decide), ?_⟩
  let B : ByteArray := ByteArray.empty.push 0x52
    ++ (ByteArray.empty.push cexKey81.size.toUInt8 ++ cexKey81)
    ++ (ByteArray.empty.push cexKey81.size.toUInt8 ++ cexKey81)
    ++ ByteArray.empty.push 0x52 ++ ByteArray.empty.push OP_CHECKMULTISIG
  have hbytes : (cexParams cexKey81).witnessScript.bytes = B := by
    simpa [B] using cexParams_witnessScript cexKey81
  have hsize : B.size = 167 := by decide
  have d0 : Bitcoin.Data.decodeOp B 0 = some (.const 2, 1) := by decide
  have d1 : Bitcoin.Data.decodeOp B 1 = some (.const 1, 2) := by decide
  have d2 : Bitcoin.Data.decodeOp B 2 = some (.push (B.extract 3 78), 78) := by decide
  have d3 : Bitcoin.Data.decodeOp B 78 = some (.push (B.extract 79 154), 154) := by decide
  have d4 : Bitcoin.Data.decodeOp B 154 = some (.push (B.extract 155 167), 167) := by decide
  unfold Bitcoin.Data.Script.parse
  rw [hbytes, hsize]
  rw [parseWith_step B 0 1 166 [] (.const 2) (by rw [hsize]; omega) d0]
  rw [parseWith_step B 1 2 165 [.const 2] (.const 1) (by rw [hsize]; omega) d1]
  rw [parseWith_step B 2 78 164 [.const 1, .const 2]
    (.push (B.extract 3 78)) (by rw [hsize]; omega) d2]
  rw [parseWith_step B 78 154 163
    [.push (B.extract 3 78), .const 1, .const 2]
    (.push (B.extract 79 154)) (by rw [hsize]; omega) d3]
  rw [parseWith_step B 154 167 162
    [.push (B.extract 79 154), .push (B.extract 3 78), .const 1, .const 2]
    (.push (B.extract 155 167)) (by rw [hsize]; omega) d4]
  simp [Bitcoin.Data.Script.parse.parseWith, hsize]

end LnLean.Proofs.ModelHardening.F02
