import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam
import LnLean.Crypto.Model

/-!
# LnLean.Proofs.WaveD.D41

**English claim (catalog `LN-L1-001`).**  The funding output is P2WSH over the
BOLT 3 2-of-2 funding witness script.  This module proves the exact byte
decomposition of the funding `scriptPubKey`:

`OP_0 <0x20> SHA256(witnessScript)`

i.e. witness version 0 followed by a direct 32-byte push of the SHA-256 of the
funding witness script `2 <funding_pubkey1> <funding_pubkey2> 2
OP_CHECKMULTISIG`.  Concretely, the script bytes are
`[0x00, 0x20] ++ witnessScriptHash`; the leading `0x00` is the version-0
witness program marker (`OP_0`), `0x20` is the 32-byte push opcode, and the
remaining 32 bytes are the program.  The proof is parametric in the stored
`witnessScriptHash` field and therefore does not assume SHA-256 internally.

The last step, identifying `witnessScriptHash` with `SHA256(witnessScript)`,
is **not** a theorem of the model: `FundingParams.witnessScriptHash` is an
unconstrained byte array and `FundingParams` has no field or invariant tying
it to the witness script.  The two results that make this precise are:

* `waveD_d41_scriptPubKey_sha256_shape`: a conditional theorem, taking a
  `PrimitiveModel` and the explicit hypothesis
  `p.witnessScriptHash = M.sha256 p.witnessScript.bytes`, which yields the
  exact 34-byte `OP_0 <0x20> SHA256(witnessScript)` shape;
* `waveD_d41_no_global_sha256_bridge`: a mechanized negative result showing
  that no single hash function can satisfy that bridge for every well-formed
  `FundingParams`, because two well-formed parameter sets with the *same*
  witness script can carry different `witnessScriptHash` values.

Anchors:
* BOLT 3, "Funding Transaction Output"
  (`refs/bolts/03-transactions.md:75-83`).
* BIP 141: `OP_0 <32-byte-witness-program>` for witness version 0, P2WSH.
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:849-866`
  (`make_funding_redeemscript`, `make_funding_redeemscript_from_slices`).
* `refs/rust-lightning/lightning/src/ln/channel.rs:2711-2725`
  (`get_funding_txo`, funding P2WSH output).

Not modelled: the concrete SHA-256 compression function and digest values
(the hash is an interface parameter of `LnLean.Crypto.PrimitiveModel`), L1
consensus/confirmation, and script execution/spendability.
-/

namespace LnLean.Proofs.WaveD.D41

set_option autoImplicit false

-- OBLIGATION: LN-WD-D41

open Bitcoin.Data
open LnLean.Bitcoin

/-! ## The two-byte P2WSH prefix: witness version 0 and a 32-byte push -/

/-- `OP_0 <0x20>`, the BIP 141 witness-version-0 / 32-byte-program prefix. -/
def waveD_d41_fundingPrefix : ByteArray :=
  (ByteArray.empty.push OP_0).push 0x20

/-- The funding prefix is exactly two bytes. -/
theorem waveD_d41_fundingPrefix_size :
    waveD_d41_fundingPrefix.size = 2 := by
  decide

/-- Its first byte is `OP_0` (`0x00`), the witness version 0 marker. -/
theorem waveD_d41_fundingPrefix_version :
    waveD_d41_fundingPrefix.extract 0 1 = [0x00].toByteArray := by
  decide

/-- Its second byte is `0x20`, the push length for a 32-byte witness program. -/
theorem waveD_d41_fundingPrefix_push32 :
    waveD_d41_fundingPrefix.extract 1 2 = [0x20].toByteArray := by
  decide

/-! ## Exact byte shape of the funding `scriptPubKey` -/

/-- The funding `scriptPubKey` is exactly `OP_0 <0x20> witnessScriptHash`. -/
theorem waveD_d41_fundingScriptPubKey_bytes (p : FundingParams) :
    p.fundingScriptPubKey.bytes =
      waveD_d41_fundingPrefix ++ p.witnessScriptHash := rfl

/-- The same decomposition for the L1 funding-output record: its
`scriptPubKey` is the P2WSH wrapper over the stored funding hash. -/
theorem waveD_d41_toFundingOutput_script (p : FundingParams) (txid : ByteArray)
    (index : Nat) :
    (p.toFundingOutput txid index).scriptPubKey = p.fundingScriptPubKey := rfl

/-- The recorded funding output's bytes have the exact P2WSH shape. -/
theorem waveD_d41_toFundingOutput_bytes (p : FundingParams) (txid : ByteArray)
    (index : Nat) :
    (p.toFundingOutput txid index).scriptPubKey.bytes =
      waveD_d41_fundingPrefix ++ p.witnessScriptHash :=
  waveD_d41_fundingScriptPubKey_bytes p

/-- The `scriptPubKey` is 34 bytes exactly when the stored program is 32
bytes (the BIP 141 P2WSH length). -/
theorem waveD_d41_fundingScriptPubKey_size_iff (p : FundingParams) :
    p.fundingScriptPubKey.bytes.size = 34 ↔
      p.witnessScriptHash.size = 32 := by
  have h : p.fundingScriptPubKey.bytes.size =
      waveD_d41_fundingPrefix.size + p.witnessScriptHash.size := by
    rw [waveD_d41_fundingScriptPubKey_bytes]
    simp [ByteArray.size_append]
  rw [h, waveD_d41_fundingPrefix_size]
  omega

/-- For well-formed funding parameters the `scriptPubKey` is 34 bytes. -/
theorem waveD_d41_fundingScriptPubKey_size_of_wellFormed (p : FundingParams)
    (hwf : p.WellFormed) :
    p.fundingScriptPubKey.bytes.size = 34 :=
  (waveD_d41_fundingScriptPubKey_size_iff p).mpr
    (by rcases hwf with ⟨-, -, -, -, h32, -⟩; exact h32)

/-- **P2WSH shape.**  For well-formed parameters the funding `scriptPubKey`
is witness version 0 followed by a 32-byte witness program, and that program
is exactly the stored funding witness-script hash. -/
theorem waveD_d41_scriptPubKey_is_p2wsh (p : FundingParams)
    (hwf : p.WellFormed) :
    ∃ program : ByteArray,
      program.size = 32 ∧
      p.fundingScriptPubKey.bytes = waveD_d41_fundingPrefix ++ program := by
  rcases hwf with ⟨-, -, -, -, h32, -⟩
  exact ⟨p.witnessScriptHash, h32, waveD_d41_fundingScriptPubKey_bytes p⟩

/-! ## Reading back the version and the program -/

/-- The first byte of the funding `scriptPubKey` is witness version 0
(`OP_0`). -/
theorem waveD_d41_scriptPubKey_version (p : FundingParams) :
    (p.fundingScriptPubKey.bytes).extract 0 1 = [0x00].toByteArray := by
  rw [waveD_d41_fundingScriptPubKey_bytes, ByteArray.extract_append]
  rw [waveD_d41_fundingPrefix_size]
  rw [show waveD_d41_fundingPrefix.extract 0 1 = [0x00].toByteArray from
    waveD_d41_fundingPrefix_version]
  rw [show p.witnessScriptHash.extract (0 - 2) (1 - 2) = ByteArray.empty from by
    rw [ByteArray.extract_eq_empty_iff]
    simp]
  rw [ByteArray.append_empty]

/-- The second byte of the funding `scriptPubKey` is `0x20`, the 32-byte push
opcode. -/
theorem waveD_d41_scriptPubKey_push32 (p : FundingParams) :
    (p.fundingScriptPubKey.bytes).extract 1 2 = [0x20].toByteArray := by
  rw [waveD_d41_fundingScriptPubKey_bytes, ByteArray.extract_append]
  rw [waveD_d41_fundingPrefix_size]
  rw [show waveD_d41_fundingPrefix.extract 1 2 = [0x20].toByteArray from
    waveD_d41_fundingPrefix_push32]
  rw [show p.witnessScriptHash.extract (1 - 2) (2 - 2) = ByteArray.empty from by
    rw [ByteArray.extract_eq_empty_iff]
    simp]
  rw [ByteArray.append_empty]

/-- The program following the two-byte prefix is exactly the stored
witness-script hash. -/
theorem waveD_d41_scriptPubKey_program (p : FundingParams) :
    (p.fundingScriptPubKey.bytes).extract 2 (2 + p.witnessScriptHash.size) =
      p.witnessScriptHash := by
  rw [waveD_d41_fundingScriptPubKey_bytes, ByteArray.extract_append]
  rw [waveD_d41_fundingPrefix_size]
  rw [show waveD_d41_fundingPrefix.extract 2
      (2 + p.witnessScriptHash.size) = ByteArray.empty from by
    rw [ByteArray.extract_eq_empty_iff]
    simp [waveD_d41_fundingPrefix, ByteArray.size_push, ByteArray.size_empty]]
  rw [ByteArray.empty_append]
  rw [show 2 + p.witnessScriptHash.size - 2 = p.witnessScriptHash.size from by
    omega]
  rw [ByteArray.extract_zero_size]

/-- For a 32-byte program the extraction window is exactly the BIP 141
34-byte script: bytes `2..34` are the witness program. -/
theorem waveD_d41_scriptPubKey_program_of_size (p : FundingParams)
    (h32 : p.witnessScriptHash.size = 32) :
    (p.fundingScriptPubKey.bytes).extract 2 34 = p.witnessScriptHash := by
  rw [show (34 : Nat) = 2 + p.witnessScriptHash.size from by omega]
  exact waveD_d41_scriptPubKey_program p

/-- The P2WSH wrapper is injective on the program: any decomposition of the
funding `scriptPubKey` into the same two-byte prefix and a program yields
exactly the stored witness-script hash.  In particular the output commits to
one program, not a family of programs. -/
theorem waveD_d41_scriptPubKey_unique_program (p : FundingParams)
    (program : ByteArray)
    (h : p.fundingScriptPubKey.bytes =
      waveD_d41_fundingPrefix ++ program) :
    program = p.witnessScriptHash := by
  have hb : waveD_d41_fundingPrefix ++ program =
      waveD_d41_fundingPrefix ++ p.witnessScriptHash := by
    rw [← h, waveD_d41_fundingScriptPubKey_bytes p]
  exact LnLean.Crypto.append_left_cancel hb

/-! ## Parser-level decomposition: `OP_0` then a 32-byte push

These lemmas expose the wave-A `Bitcoin.Data.Script.parse` view of the
`scriptPubKey`.  They do not add a `ScriptInstr` constructor; they show that
the concrete parser decodes the version-0 marker as an empty push and the
`0x20` byte as a push of exactly the fundings program. -/

private theorem waveD_d41_getElem?_append_lt (a b : ByteArray) (i : Nat)
    (h : i < a.size) :
    (a ++ b)[i]? = a[i]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append,
      ite_eq_left (by simpa using h)]
  rw [show a[i]? = a.data[i]? from rfl]

private theorem waveD_d41_getElem?_push_eq (a : ByteArray) (x : UInt8) :
    (a.push x)[a.size]? = some x := by
  rw [show (a.push x)[a.size]? = (a.push x).data[a.size]? from rfl,
      ByteArray.data_push, Array.getElem?_push,
      ite_eq_left (show a.size = a.data.size from rfl)]

/-- Folding `get!` over a contiguous range is `extract`. -/
private theorem waveD_d41_foldl_range_get_eq_extract (b : ByteArray)
    (i n : Nat) (h : i + n ≤ b.size) :
    (List.range n).foldl (fun acc k => acc.push (b.get! (i + k)))
        ByteArray.empty =
      b.extract i (i + n) := by
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
        show max (i + n) (i + n + 1) = i + n + 1 from
          Nat.max_eq_right (by omega)] at hsplit
    rw [show i + (n + 1) = i + n + 1 from by omega]
    exact hsplit.symm

/-- `takeBytes` of a contiguous in-range window is `extract`. -/
private theorem waveD_d41_takeBytes_eq_extract (b : ByteArray) (i n : Nat)
    (h : i + n ≤ b.size) :
    Bitcoin.Data.takeBytes b i n = some (b.extract i (i + n)) := by
  unfold Bitcoin.Data.takeBytes
  rw [ite_eq_left h, waveD_d41_foldl_range_get_eq_extract b i n h]

/-- Extraction immediately after the two-byte P2WSH prefix returns the
program, regardless of any trailing bytes. -/
private theorem waveD_d41_extract_prefix_hash (hash rest : ByteArray) :
    (waveD_d41_fundingPrefix ++ hash ++ rest).extract 2 (2 + hash.size) =
      hash := by
  rw [ByteArray.extract_append]
  rw [show (waveD_d41_fundingPrefix ++ hash).extract 2 (2 + hash.size) =
      hash from by
    rw [ByteArray.extract_append]
    rw [waveD_d41_fundingPrefix_size]
    rw [show waveD_d41_fundingPrefix.extract 2 (2 + hash.size) =
        ByteArray.empty from by
      rw [ByteArray.extract_eq_empty_iff]
      simp [waveD_d41_fundingPrefix, ByteArray.size_push,
        ByteArray.size_empty]]
    rw [ByteArray.empty_append]
    rw [show 2 + hash.size - 2 = hash.size from by omega]
    rw [ByteArray.extract_zero_size]]
  rw [show 2 - (waveD_d41_fundingPrefix ++ hash).size = 0 from by
    simp [waveD_d41_fundingPrefix, ByteArray.size_append, ByteArray.size_push,
      ByteArray.size_empty]]
  rw [show 2 + hash.size - (waveD_d41_fundingPrefix ++ hash).size = 0 from by
    simp [waveD_d41_fundingPrefix, ByteArray.size_append, ByteArray.size_push,
      ByteArray.size_empty]]
  rw [show rest.extract 0 0 = ByteArray.empty from by
    rw [ByteArray.extract_eq_empty_iff]
    simp]
  rw [ByteArray.append_empty]

/-- `decodeOp` reads the version-0 marker as an empty push. -/
private theorem waveD_d41_decodeOp_version0 (rest : ByteArray) :
    Bitcoin.Data.decodeOp (ByteArray.empty.push OP_0 ++ rest) 0 =
      some (.push ByteArray.empty, 1) := by
  unfold Bitcoin.Data.decodeOp
  rw [show (ByteArray.empty.push OP_0 ++ rest)[0]? = some OP_0 from by
    rw [waveD_d41_getElem?_append_lt (ByteArray.empty.push OP_0) rest 0
      (by simp)]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl]
    exact waveD_d41_getElem?_push_eq _ _]
  simp [OP_0]

/-- `decodeOp` reads `0x20` as a direct push of the 32-byte program. -/
private theorem waveD_d41_decodeOp_push32 (hash rest : ByteArray)
    (h : hash.size = 32) :
    Bitcoin.Data.decodeOp
        (waveD_d41_fundingPrefix ++ hash ++ rest) 1 =
      some (.push hash, 1 + 1 + 32) := by
  unfold Bitcoin.Data.decodeOp
  rw [show (waveD_d41_fundingPrefix ++ hash ++ rest)[1]? = some 0x20 from by
    rw [show waveD_d41_fundingPrefix ++ hash ++ rest =
        waveD_d41_fundingPrefix ++ (hash ++ rest) from by
      simp [ByteArray.append_assoc]]
    rw [waveD_d41_getElem?_append_lt waveD_d41_fundingPrefix (hash ++ rest) 1
      (by decide)]
    decide]
  have htake : Bitcoin.Data.takeBytes
      (waveD_d41_fundingPrefix ++ hash ++ rest) 2 32 = some hash := by
    rw [show (32 : Nat) = hash.size from by omega]
    rw [waveD_d41_takeBytes_eq_extract]
    · rw [waveD_d41_extract_prefix_hash hash rest]
    · simp [waveD_d41_fundingPrefix, ByteArray.size_append,
        ByteArray.size_push, ByteArray.size_empty, h]
  simp only [show (0x20 : UInt8).toNat = 32 from rfl,
    show (32 : Nat) ≠ 0 from by decide,
    show (32 : Nat) ≤ 0x4b from by decide,
    ite_true, htake]
  rfl

private theorem waveD_d41_parseWith_step (b : ByteArray) (i i' fuel : Nat)
    (acc : List Bitcoin.Data.ScriptInstr)
    (op : Bitcoin.Data.ScriptInstr) (hi : i < b.size)
    (hdec : Bitcoin.Data.decodeOp b i = some (op, i')) :
    Bitcoin.Data.Script.parse.parseWith b (fuel + 1) i acc =
      Bitcoin.Data.Script.parse.parseWith b fuel i' (op :: acc) := by
  have hni : ¬ b.size ≤ i := by omega
  simp [Bitcoin.Data.Script.parse.parseWith, hni, hdec]

/-- **Parser-level decomposition.**  For a 32-byte program the concrete
wave-A parser decodes the funding `scriptPubKey` as an empty push (the `OP_0`
version marker) followed by a push of exactly the witness-script hash. -/
theorem waveD_d41_scriptPubKey_parse (p : FundingParams)
    (h32 : p.witnessScriptHash.size = 32) :
    p.fundingScriptPubKey.parse =
      some [.push ByteArray.empty, .push p.witnessScriptHash] := by
  unfold Bitcoin.Data.Script.parse
  rw [show p.fundingScriptPubKey.bytes =
      waveD_d41_fundingPrefix ++ p.witnessScriptHash from
    waveD_d41_fundingScriptPubKey_bytes p]
  rw [show (waveD_d41_fundingPrefix ++ p.witnessScriptHash).size = 34 from by
    simp [waveD_d41_fundingPrefix, ByteArray.size_append,
      ByteArray.size_push, ByteArray.size_empty, h32]]
  have d0 : Bitcoin.Data.decodeOp
      (waveD_d41_fundingPrefix ++ p.witnessScriptHash) 0 =
      some (.push ByteArray.empty, 1) := by
    rw [show waveD_d41_fundingPrefix =
        (ByteArray.empty.push OP_0) ++ (ByteArray.empty.push 0x20) from by
      decide,
      ByteArray.append_assoc]
    exact waveD_d41_decodeOp_version0
      ((ByteArray.empty.push 0x20) ++ p.witnessScriptHash)
  have d1 : Bitcoin.Data.decodeOp
      (waveD_d41_fundingPrefix ++ p.witnessScriptHash) 1 =
      some (.push p.witnessScriptHash, 34) := by
    simpa using waveD_d41_decodeOp_push32 p.witnessScriptHash ByteArray.empty h32
  rw [waveD_d41_parseWith_step
    (waveD_d41_fundingPrefix ++ p.witnessScriptHash) 0 1 33 []
    (.push ByteArray.empty)
    (by simp [waveD_d41_fundingPrefix, ByteArray.size_append,
      ByteArray.size_push, ByteArray.size_empty, h32]) d0]
  rw [waveD_d41_parseWith_step
    (waveD_d41_fundingPrefix ++ p.witnessScriptHash) 1 34 32
    [.push ByteArray.empty] (.push p.witnessScriptHash)
    (by simp [waveD_d41_fundingPrefix, ByteArray.size_append,
      ByteArray.size_push, ByteArray.size_empty, h32]) d1]
  simp [Bitcoin.Data.Script.parse.parseWith, waveD_d41_fundingPrefix,
    ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty, h32]

/-! ## Conditional identification with SHA-256

The model stores `witnessScriptHash` as a parameter.  The following theorem
identifies it with `SHA256(witnessScript)` under the explicit bridge
hypothesis naming the missing crypto link. -/

/-- **Exact `OP_0 <0x20> SHA256(witnessScript)` shape.**  Given a primitive
model and the hypothesis that the stored hash is the model's SHA-256 of the
funding witness script, the funding `scriptPubKey` is exactly the 34-byte
P2WSH script whose program is that SHA-256 digest. -/
theorem waveD_d41_scriptPubKey_sha256_shape
    (M : LnLean.Crypto.PrimitiveModel) (p : FundingParams)
    (hhash : p.witnessScriptHash = M.sha256 p.witnessScript.bytes) :
    p.fundingScriptPubKey.bytes =
        waveD_d41_fundingPrefix ++ M.sha256 p.witnessScript.bytes ∧
      (p.fundingScriptPubKey.bytes).extract 2 34 =
        M.sha256 p.witnessScript.bytes ∧
      (M.sha256 p.witnessScript.bytes).size = 32 ∧
      p.fundingScriptPubKey.bytes.size = 34 := by
  have h32 := M.sha256_size p.witnessScript.bytes
  refine ⟨?_, ?_, h32, ?_⟩
  · rw [waveD_d41_fundingScriptPubKey_bytes, hhash]
  · rw [show (34 : Nat) = 2 + p.witnessScriptHash.size from by
      rw [hhash, M.sha256_size]]
    rw [waveD_d41_scriptPubKey_program p, hhash]
  · rw [show p.fundingScriptPubKey.bytes.size =
        2 + p.witnessScriptHash.size from by
      rw [waveD_d41_fundingScriptPubKey_bytes]
      simp [ByteArray.size_append, waveD_d41_fundingPrefix_size], hhash]
    omega

/-- Conditional SHA-256 shape at the L1 funding-output record. -/
theorem waveD_d41_toFundingOutput_sha256_shape
    (M : LnLean.Crypto.PrimitiveModel) (p : FundingParams)
    (txid : ByteArray) (index : Nat)
    (hhash : p.witnessScriptHash = M.sha256 p.witnessScript.bytes) :
    (p.toFundingOutput txid index).scriptPubKey.bytes =
      waveD_d41_fundingPrefix ++ M.sha256 p.witnessScript.bytes := by
  rw [waveD_d41_toFundingOutput_script p txid index,
    waveD_d41_fundingScriptPubKey_bytes p, hhash]

/-- Conditional SHA-256 shape for a confirmed funding output. -/
theorem waveD_d41_FundingConfirmed_sha256_shape
    (M : LnLean.Crypto.PrimitiveModel) (p : FundingParams)
    {tx : Bitcoin.Data.Tx} {index : Nat}
    (hhash : p.witnessScriptHash = M.sha256 p.witnessScript.bytes)
    (h : FundingConfirmed p tx index) :
    ∃ out : Bitcoin.Data.TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        waveD_d41_fundingPrefix ++ M.sha256 p.witnessScript.bytes ∧
      out.scriptPubKey.bytes.size = 34 := by
  obtain ⟨out, hout, -, hscript⟩ := h
  refine ⟨out, hout, ?_, ?_⟩
  · rw [hscript, waveD_d41_fundingScriptPubKey_bytes p, hhash]
  · rw [hscript]
    exact (waveD_d41_fundingScriptPubKey_size_iff p).mpr (by
      rw [hhash, M.sha256_size])

/-- Any confirmed funding output has the exact P2WSH byte shape over the
stored hash. -/
theorem waveD_d41_FundingConfirmed_shape {p : FundingParams}
    {tx : Bitcoin.Data.Tx} {index : Nat}
    (h : FundingConfirmed p tx index) :
    ∃ out : Bitcoin.Data.TxOut,
      tx.vout[index]? = some out ∧
      out.scriptPubKey.bytes =
        waveD_d41_fundingPrefix ++ p.witnessScriptHash := by
  obtain ⟨out, hout, -, hscript⟩ := h
  exact ⟨out, hout, by rw [hscript, waveD_d41_fundingScriptPubKey_bytes p]⟩

/-! ## The missing bridge is a real gap, not a proof obligation

`FundingParams.witnessScriptHash` is unconstrained.  Two well-formed parameter
sets can share the same 2-of-2 witness script and still carry different
stored hashes, so no single hash function is determined by the witness script
alone in the current model.  This is a precise negative result; the positive
statement above is conditional on the explicit bridge hypothesis. -/

private def waveD_d41_cexKey : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate 33 (0 : UInt8)))

private def waveD_d41_cexHashA : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate 32 (0 : UInt8)))

private def waveD_d41_cexHashB : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate 32 (1 : UInt8)))

private theorem waveD_d41_cexKey_size : waveD_d41_cexKey.size = 33 := by
  decide

private theorem waveD_d41_cexHashA_size : waveD_d41_cexHashA.size = 32 := by
  decide

private theorem waveD_d41_cexHashB_size : waveD_d41_cexHashB.size = 32 := by
  decide

private theorem waveD_d41_cexHashA_ne_cexHashB :
    waveD_d41_cexHashA ≠ waveD_d41_cexHashB := by
  decide

/-- Well-formed funding parameters with a fixed 33-byte key and hash `A`. -/
private def waveD_d41_cexP : FundingParams :=
  { fundingSatoshis := 0
    pushMsat := ⟨0⟩
    localFundingKey := ⟨waveD_d41_cexKey⟩
    remoteFundingKey := ⟨waveD_d41_cexKey⟩
    witnessScriptHash := waveD_d41_cexHashA
    temporaryChannelId := ⟨⟨ByteArray.empty⟩⟩ }

/-- The same parameters with hash `B` instead of `A`. -/
private def waveD_d41_cexQ : FundingParams :=
  { waveD_d41_cexP with witnessScriptHash := waveD_d41_cexHashB }

private theorem waveD_d41_cexP_wellFormed : waveD_d41_cexP.WellFormed := by
  unfold FundingParams.WellFormed
  simp [waveD_d41_cexP, PubKey.Valid, waveD_d41_cexKey_size,
    waveD_d41_cexHashA_size, Bitcoin.Data.MAX_MONEY, Bitcoin.Data.COIN]

private theorem waveD_d41_cexQ_wellFormed : waveD_d41_cexQ.WellFormed := by
  unfold FundingParams.WellFormed
  simp [waveD_d41_cexQ, waveD_d41_cexP, PubKey.Valid,
    waveD_d41_cexKey_size, waveD_d41_cexHashB_size,
    Bitcoin.Data.MAX_MONEY, Bitcoin.Data.COIN]

private theorem waveD_d41_cexQ_witnessScript :
    waveD_d41_cexQ.witnessScript = waveD_d41_cexP.witnessScript := by
  simp [waveD_d41_cexQ, FundingParams.witnessScript]

/-- **Underdetermination of the stored hash.**  There are two well-formed
funding parameter sets with the same 2-of-2 witness script but different
`witnessScriptHash` values; the model alone cannot identify the stored hash
with the SHA-256 of the script. -/
theorem waveD_d41_witnessScriptHash_underdetermined :
    ∃ p q : FundingParams,
      p.WellFormed ∧ q.WellFormed ∧
      p.witnessScript = q.witnessScript ∧
      p.witnessScriptHash ≠ q.witnessScriptHash := by
  refine ⟨waveD_d41_cexP, waveD_d41_cexQ,
    waveD_d41_cexP_wellFormed, waveD_d41_cexQ_wellFormed, ?_, ?_⟩
  · rw [waveD_d41_cexQ_witnessScript]
  · simp [waveD_d41_cexP, waveD_d41_cexQ,
      waveD_d41_cexHashA_ne_cexHashB]

/-- **No global SHA-256 bridge.**  No single function maps every well-formed
funding witness script to its stored `witnessScriptHash`.  The missing model
field is a constraint such as
`p.witnessScriptHash = sha256 p.witnessScript.bytes`. -/
theorem waveD_d41_no_global_sha256_bridge :
    ¬ ∃ sha256 : ByteArray → ByteArray,
      ∀ p : FundingParams,
        p.WellFormed → p.witnessScriptHash = sha256 p.witnessScript.bytes := by
  rintro ⟨sha256, h⟩
  obtain ⟨p, q, hwp, hwq, hscript, hne⟩ :=
    waveD_d41_witnessScriptHash_underdetermined
  have hp := h p hwp
  have hq := h q hwq
  apply hne
  rw [hp, hq, hscript]

/-- Conditional commitment: if the stored hash is the SHA-256 of the funding
witness script and SHA-256 is injective on the modelled byte strings (an
explicit global hypothesis, not a field of `PrimitiveModel`), then any script
whose SHA-256 equals the stored hash is exactly the funding witness script. -/
theorem waveD_d41_revealed_script_eq_witnessScript
    (sha256 : ByteArray → ByteArray)
    (hinj : ∀ a b : ByteArray, sha256 a = sha256 b → a = b)
    (p : FundingParams)
    (hhash : p.witnessScriptHash = sha256 p.witnessScript.bytes)
    (revealed : ByteArray)
    (hreveal : sha256 revealed = p.witnessScriptHash) :
    revealed = p.witnessScript.bytes := by
  apply hinj
  rw [hreveal, hhash]

end LnLean.Proofs.WaveD.D41
