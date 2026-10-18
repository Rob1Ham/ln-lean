import Bitcoin.Interpreter.Defs
import LnLean.Proofs.Bitcoin.SpendTargets

/-!
# Bridge from the `SpendTargets` interpreter-law model to the vendored Bitcoin interpreter

This module is the Wave-5 (lane `S5-L1-INTERP`) companion of
`LnLean.Proofs.Bitcoin.SpendTargets`.  The model there executes a small
structured program (`Instr` / `Stmt`) under explicit `InterpreterLaws`.
Here we connect that program, byte for byte, to the real, fuel-bounded
transliteration of Core's `EvalScript` in
`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean`.

What is mechanized:

* the model serializer `serializeStmts` agrees with the vendor canonical
  printer `Bitcoin.Script.Parser.serializeOpcodes` on the well-formed
  funding and `to_local` programs;
* the vendor parser `parseWire` recovers the canonical `WireOp` list
  (`wireOpsFrom`) from those bytes, with the exact `next` offsets;
* the vendor `evalFrom` run of the funding 2-of-2 script is computed,
  including the full `OP_CHECKMULTISIG` path (`cmsLoop`, `cmsCleanup`,
  encoding checks, script-number decode), and agrees with the model
  stack machine;
* `evalScriptBytes`, `executeWitnessScript` and the P2WSH branch of
  `verifyWitnessProgram` are reduced to that computation, so the real
  `verifyWitnessProgram` returns `.ok` under the same signature-checker
  hypotheses that establish the model's `P2WSHSpend` (one direction; no
  converse or negative-direction claim is made here);
* the `to_local` `OP_ELSE` (delayed) branch is computed through
  `OP_IF`/`OP_ELSE`/`OP_ENDIF`, `OP_CSV`, `OP_DROP` and
  `OP_CHECKSIG` on the concrete wire list, under explicit decoding and
  sequence-check hypotheses (`evalFrom_toLocalWireOps_delayed`,
  `verifyWitnessProgram_toLocal_delayed`, and
  `toLocal_delayed_interpreters_agree`).

What is deliberately *not* mechanized (see the final section and the
report `agents/reports/swarm5/S5-L1-INTERP.md`):

* BIP 143 sighash construction — the checker receives the sighash
  `msg` from the caller, exactly as in the model;
* constructing the decoded delay `n` and the `LocktimeEnv` from raw
  transaction/commitment data: the delayed-branch theorems take
  `decodeNum ... = .ok n`, `0 ≤ n`, the disable-bit test and
  `checkSequenceDef chk.env n = true` as explicit hypotheses (these are
  decidable for concrete `csv`/environment values, and `csv < 0x8000`
  keeps the fixed-width delay push non-negative under sign-magnitude
  decoding);
* the `to_local` revocation branch (`OP_IF` true path) at the vendor
  execution level; its model-side theorem already exists in
  `SpendTargets`, but no vendor `evalFrom` computation is claimed here;
* any change to the vendored sources.  The bridge is a client of the
  frozen vendor API.
-/

namespace LnLean.Proofs.Bitcoin.InterpreterBridgeTargets

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets
open LnLean.Proofs.Bitcoin.SpendTargets

/-! ## 1. Serialization: model → vendor canonical printer -/

theorem empty_push_eq (x : UInt8) :
    ByteArray.empty.push x = [x].toByteArray := rfl

theorem push_eq_append (a : ByteArray) (x : UInt8) :
    a.push x = a ++ [x].toByteArray :=
  ByteArray.append_toByteArray_singleton.symm

theorem pushData_eq_pushBytesWire (d : ByteArray) (h : d.size ≤ 75) :
    pushData d = pushBytesWire d := by
  cases hd : d.size with
  | zero => simp [pushData, pushBytesWire, lenBytes, hd, empty_push_eq]
  | succ n =>
    have hle : n + 1 ≤ 75 := by omega
    simp [pushData, pushBytesWire, lenBytes, hd, hle, empty_push_eq]

theorem serializeOpcodes_append (a b : List Opcode) :
    serializeOpcodes (a ++ b) = serializeOpcodes a ++ serializeOpcodes b := by
  induction a with
  | nil => simp [serializeOpcodes]
  | cons x xs ih =>
    calc
      serializeOpcodes ((x :: xs) ++ b)
          = serializeOpcode x ++ serializeOpcodes (xs ++ b) := rfl
      _ = serializeOpcode x ++ (serializeOpcodes xs ++ serializeOpcodes b) := by rw [ih]
      _ = (serializeOpcode x ++ serializeOpcodes xs) ++ serializeOpcodes b := by
            rw [ByteArray.append_assoc]
      _ = serializeOpcodes (x :: xs) ++ serializeOpcodes b := rfl

theorem serializeOp_singleton (n : Nat) (h : n < 256) :
    serializeOpcodes [Opcode.op ⟨n, h⟩] =
      ByteArray.empty.push (OfNat.ofNat n : UInt8) := by
  simp [serializeOpcodes, serializeOpcode_op, empty_push_eq]
  rfl

theorem serializePush_singleton (d : ByteArray) :
    serializeOpcodes [Opcode.pushBytes d] = pushBytesWire d := by
  simp [serializeOpcodes, serializeOpcode_pushBytes, pushBytesWire]

theorem serializeNum_two :
    serializeOpcodes [Opcode.pushNum 2] = ByteArray.empty.push (0x52 : UInt8) := by
  simp [serializeOpcodes, serializeOpcode_pushNum, empty_push_eq]

theorem foldr_serialize_acc : ∀ (ops : List Opcode) (b : ByteArray),
    ops.foldr (fun o acc => serializeOpcode o ++ acc) b =
      serializeOpcodes ops ++ b
  | [], b => by simp [serializeOpcodes]
  | x :: xs, b => by
    simp only [List.foldr_cons, serializeOpcodes]
    rw [foldr_serialize_acc xs b, foldr_serialize_acc xs ByteArray.empty,
      ByteArray.append_empty, ByteArray.append_assoc]

theorem foldl_serialize_gen (X : ByteArray) :
    ∀ p : List Stmt,
      p.foldl (fun acc s => acc ++ s.serialize) X = X ++ serializeStmts p
  | [] => by simp [serializeStmts]
  | s :: rest => by
    have ih := foldl_serialize_gen (X ++ s.serialize) rest
    have hcons : serializeStmts (s :: rest) = s.serialize ++ serializeStmts rest := by
      simpa [serializeStmts] using foldl_serialize_gen s.serialize rest
    simp only [List.foldl_cons]
    rw [ih, hcons, ByteArray.append_assoc]

theorem serializeStmts_cons (s : Stmt) (p : List Stmt) :
    serializeStmts (s :: p) = s.serialize ++ serializeStmts p := by
  simpa [serializeStmts] using foldl_serialize_gen s.serialize p

/-- Well-formed instructions for the byte-level bridge.  The model's `num`
is restricted to `OP_2`, the only number push in the funding script; the
`to_local` script uses no number pushes. -/
def InstrWF : Instr → Prop
  | .push d => d.size ≤ 75
  | .num n => n = 2
  | _ => True

def StmtWF : Stmt → Prop
  | .basic i => InstrWF i
  | .ite t e => (∀ s ∈ t, StmtWF s) ∧ (∀ s ∈ e, StmtWF s)

def ProgWF (p : List Stmt) : Prop := ∀ s ∈ p, StmtWF s

def instrToOpcode : Instr → Opcode
  | .push d => .pushBytes d
  | .num n => .pushNum n
  | .dup => .op ⟨0x76, by decide⟩
  | .drop => .op ⟨0x75, by decide⟩
  | .hash160 => .op ⟨0xa9, by decide⟩
  | .sha256 => .op ⟨0xa8, by decide⟩
  | .equal => .op ⟨0x87, by decide⟩
  | .equalVerify => .op ⟨0x88, by decide⟩
  | .checkSig => .op ⟨0xac, by decide⟩
  | .checkMultiSig => .op ⟨0xae, by decide⟩
  | .csv => .op ⟨0xb2, by decide⟩
  | .cltv => .op ⟨0xb1, by decide⟩

mutual
def stmtToOps : Stmt → List Opcode
  | .basic i => [instrToOpcode i]
  | .ite t e =>
      Opcode.op ⟨0x63, by decide⟩ :: stmtListToOps t ++
        [Opcode.op ⟨0x67, by decide⟩] ++ stmtListToOps e ++
        [Opcode.op ⟨0x68, by decide⟩]

def stmtListToOps : List Stmt → List Opcode
  | [] => []
  | s :: rest => stmtToOps s ++ stmtListToOps rest
end

mutual
def serializeStmt_eq : (s : Stmt) → StmtWF s →
    s.serialize = serializeOpcodes (stmtToOps s)
  | s, hs => by
    cases s with
    | basic i =>
      have hi : InstrWF i := by simpa [StmtWF] using hs
      simp only [Stmt.serialize, stmtToOps]
      cases i with
      | push d =>
        have hd : d.size ≤ 75 := by simpa [InstrWF] using hi
        simp only [instrToOpcode, Instr.serialize]
        rw [serializePush_singleton, pushData_eq_pushBytesWire d hd]
      | num n =>
        have hn : n = 2 := by simpa [InstrWF] using hi
        subst hn
        simp only [instrToOpcode, Instr.serialize]
        rw [serializeNum_two]
        rfl
      | dup =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | drop =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | hash160 =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | sha256 =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | equal =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | equalVerify =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | checkSig =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | checkMultiSig =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | csv =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
      | cltv =>
        simp only [instrToOpcode, serializeOp_singleton]
        rfl
    | ite t e =>
      have ht : (∀ s ∈ t, StmtWF s) ∧ (∀ s ∈ e, StmtWF s) := by
        simpa [StmtWF] using hs
      obtain ⟨ht, he⟩ := ht
      simp only [Stmt.serialize, stmtToOps]
      rw [serializeStmts_eq_list t ht, serializeStmts_eq_list e he]
      simp only [serializeOpcodes_cons, serializeOpcodes_append, serializeOpcode_op,
        push_eq_append, ByteArray.append_assoc, ByteArray.append_empty,
        ByteArray.empty_append, serializeOpcodes, List.foldr_append, List.foldr_cons,
        List.foldr_nil, Fin.toNat_eq_val, Fin.val_mk]
      simp only [foldr_serialize_acc]
      simp only [ByteArray.append_assoc, ByteArray.append_empty, ByteArray.empty_append]
      rfl
termination_by s _ => sizeOf s

def serializeStmts_eq_list : (p : List Stmt) → ProgWF p →
    serializeStmts p = serializeOpcodes (stmtListToOps p)
  | [], _ => by simp [serializeStmts, stmtListToOps, serializeOpcodes]
  | s :: rest, hp => by
    have hs : StmtWF s := hp s (by simp)
    have hr : ProgWF rest := fun s' hm => hp s' (by simp [hm])
    rw [serializeStmts_cons, serializeStmts_eq_list rest hr, stmtListToOps,
      serializeStmt_eq s hs, serializeOpcodes_append]
termination_by p _ => sizeOf p
end

/-! ## 2. Parsing: vendor `parseWire` recovers the canonical wire ops -/

theorem wireOpsFrom_nil (off : Nat) : wireOpsFrom off [] = [] := rfl

theorem wireOpsFrom_cons (off : Nat) (o : Opcode) (tl : List Opcode) :
    wireOpsFrom off (o :: tl) =
      { ast := o, wire := wireOfAst o, next := off + (serializeOpcode o).size } ::
        wireOpsFrom (off + (serializeOpcode o).size) tl := rfl

theorem parseWireFrom_succ (f : Nat) (b : ByteArray) (i : Nat) :
    parseWireFrom (f+1) b i =
      if b.size ≤ i then some []
      else match getOp b i with
        | none => none
        | some (o, i') => (parseWireFrom f b i').map
            (fun tl => { ast := o, wire := b[i]!.toNat, next := i' } :: tl) := rfl

theorem get!_append_right (pre q : ByteArray) (hq : 0 < q.size) :
    (pre ++ q)[pre.size]! = q[0]! := by
  have hlt : pre.size < (pre ++ q).size := by
    rw [ByteArray.size_append]; omega
  rw [getElem!_pos (pre ++ q) pre.size hlt]
  rw [ByteArray.getElem_append_right (show pre.size ≤ pre.size by omega)]
  simp only [Nat.sub_self]
  rw [← getElem!_pos q 0 hq]

theorem get!_append_left (a b : ByteArray) (ha : 0 < a.size) :
    (a ++ b)[0]! = a[0]! := by
  have hlt : 0 < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) 0 hlt]
  rw [ByteArray.getElem_append_left (show 0 < a.size by omega)]
  rw [← getElem!_pos a 0 ha]

theorem parseWireFrom_mono : ∀ (f : Nat) (b : ByteArray) (i f' : Nat) (ops : List WireOp),
    f ≤ f' → parseWireFrom f b i = some ops → parseWireFrom f' b i = some ops := by
  intro f
  induction f with
  | zero =>
    intro b i f' ops _ h
    simp only [parseWireFrom] at h
    contradiction
  | succ f ih =>
    intro b i f' ops hle h
    cases f' with
    | zero => omega
    | succ f'' =>
      have hle' : f ≤ f'' := by omega
      rw [parseWireFrom_succ] at h ⊢
      by_cases hbi : b.size ≤ i
      · rw [if_pos hbi] at h ⊢
        exact h
      · rw [if_neg hbi] at h ⊢
        cases hgo : getOp b i with
        | none => simp [hgo] at h
        | some p =>
          obtain ⟨o, i'⟩ := p
          simp only [hgo, Option.map_eq_some_iff] at h ⊢
          obtain ⟨tl, htl, rfl⟩ := h
          exact ⟨tl, ih b i' f'' tl hle' htl, rfl⟩

theorem serializeOpcodes_length_le_size (ops : List Opcode) :
    ops.length ≤ (serializeOpcodes ops).size := by
  induction ops with
  | nil => simp [serializeOpcodes]
  | cons o rest ih =>
    rw [List.length_cons, serializeOpcodes_cons, ByteArray.size_append]
    have h := serializeOpcode_size o
    omega

theorem firstByte_op (c : Fin 256) :
    (serializeOpcode (Opcode.op c))[0]!.toNat = wireOfAst (Opcode.op c) := by
  simp [serializeOpcode, wireOfAst]

theorem firstByte_pushNum_two :
    (serializeOpcode (Opcode.pushNum 2))[0]!.toNat = wireOfAst (Opcode.pushNum 2) := by
  simp [serializeOpcode, wireOfAst]

theorem firstByte_toByteArray_singleton (x : UInt8) (d : ByteArray) :
    (List.toByteArray [x] ++ d)[0]! = x := by
  have h1 : (List.toByteArray [x]).size = 1 := by simp [List.size_toByteArray]
  have h0 : 0 < (List.toByteArray [x] ++ d).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos _ 0 h0]
  simp

theorem firstByte_pushBytes_small (d : ByteArray) (hpos : 0 < d.size) (hle : d.size ≤ 75) :
    (serializeOpcode (Opcode.pushBytes d))[0]!.toNat = wireOfAst (Opcode.pushBytes d) := by
  have hlen : lenBytes d.size = [d.size.toUInt8] := by
    cases hd : d.size with
    | zero => omega
    | succ n => simp [lenBytes, hd]; omega
  rw [serializeOpcode, pushBytesWire, hlen]
  simp only [wireOfAst]
  rw [if_neg (by omega : ¬ d.size = 0), if_pos hle]
  rw [show (List.toByteArray [d.size.toUInt8] ++ d)[0]! = d.size.toUInt8 from
    firstByte_toByteArray_singleton _ _]
  simp [Nat.mod_eq_of_lt (by omega : d.size < 256)]

theorem firstByte_pushBytes_zero :
    (serializeOpcode (Opcode.pushBytes ByteArray.empty))[0]!.toNat =
      wireOfAst (Opcode.pushBytes ByteArray.empty) := by
  simp [serializeOpcode, pushBytesWire, wireOfAst, lenBytes]

theorem parseWireFrom_serialize_acc (ops : List Opcode) :
    ∀ (pre : ByteArray),
      (∀ o ∈ ops, opcodeWF o) →
      (∀ o ∈ ops, (serializeOpcode o)[0]!.toNat = wireOfAst o) →
      parseWireFrom (ops.length + 1) (pre ++ serializeOpcodes ops) pre.size =
        some (wireOpsFrom pre.size ops) := by
  induction ops with
  | nil =>
    intro pre _ _
    have hz : serializeOpcodes ([] : List Opcode) = ByteArray.empty := rfl
    rw [hz, wireOpsFrom_nil, List.length_nil, parseWireFrom_succ]
    simp [ByteArray.append_empty]
  | cons o rest ih =>
    intro pre ho hw
    have ho' : opcodeWF o := ho o (by simp)
    have hw' : (serializeOpcode o)[0]!.toNat = wireOfAst o := hw o (by simp)
    have hro : ∀ x ∈ rest, opcodeWF x := fun x hx => ho x (by simp [hx])
    have hrw : ∀ x ∈ rest, (serializeOpcode x)[0]!.toNat = wireOfAst x :=
      fun x hx => hw x (by simp [hx])
    rw [serializeOpcodes_cons, wireOpsFrom_cons, List.length_cons]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 from rfl, parseWireFrom_succ]
    have hsz : 1 ≤ (serializeOpcode o).size := serializeOpcode_size o
    rw [if_neg (show ¬((pre ++ (serializeOpcode o ++ serializeOpcodes rest)).size ≤ pre.size) from by
      rw [ByteArray.size_append, ByteArray.size_append]; omega)]
    have hg := getOp_shift pre (serializeOpcode o ++ serializeOpcodes rest) 0
    rw [Nat.add_zero] at hg
    rw [hg]
    rw [getOp_serialize o (serializeOpcodes rest) ho']
    simp only [Option.map_some, Option.bind_some]
    have hrec := ih (pre ++ serializeOpcode o) hro hrw
    rw [ByteArray.size_append, ByteArray.append_assoc] at hrec
    rw [hrec]
    have hq : 0 < (serializeOpcode o ++ serializeOpcodes rest).size := by
      rw [ByteArray.size_append]; omega
    simp only [get!_append_right _ _ hq, get!_append_left _ _ hsz, hw']
    rfl

theorem parseWire_serializeOpcodes (ops : List Opcode)
    (ho : ∀ o ∈ ops, opcodeWF o)
    (hw : ∀ o ∈ ops, (serializeOpcode o)[0]!.toNat = wireOfAst o) :
    parseWire (serializeOpcodes ops) = some (wireOpsFrom 0 ops) := by
  unfold parseWire
  have h := parseWireFrom_serialize_acc ops ByteArray.empty ho hw
  have hle : ops.length + 1 ≤ (serializeOpcodes ops).size + 1 := by
    have := serializeOpcodes_length_le_size ops; omega
  exact parseWireFrom_mono _ _ _ _ _ hle (by simpa using h)

/-! ## 3. The concrete opcode streams -/

/-- Opcode stream of the BOLT 3 2-of-2 funding witness script. -/
def fundingOps (a b : PubKey) : List Opcode :=
  [ .pushNum 2, .pushBytes a.bytes, .pushBytes b.bytes, .pushNum 2,
    .op ⟨0xae, by decide⟩ ]

/-- Opcode stream of the BOLT 3 `to_local` witness script. -/
def toLocalOps (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) : List Opcode :=
  [ .op ⟨0x63, by decide⟩, .pushBytes revocationKey.bytes, .op ⟨0x67, by decide⟩,
    .pushBytes (delayBytes csv), .op ⟨0xb2, by decide⟩, .op ⟨0x75, by decide⟩,
    .pushBytes delayedPaymentKey.bytes, .op ⟨0x68, by decide⟩, .op ⟨0xac, by decide⟩ ]

theorem stmtListToOps_funding (a b : PubKey) :
    stmtListToOps (fundingProg a b) = fundingOps a b := by
  simp [fundingProg, fundingOps, stmtListToOps, stmtToOps, instrToOpcode]

theorem stmtListToOps_toLocal (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    stmtListToOps (toLocalProg revocationKey delayedPaymentKey csv) =
      toLocalOps revocationKey delayedPaymentKey csv := by
  simp [toLocalProg, toLocalOps, stmtListToOps, stmtToOps, instrToOpcode]

theorem fundingProg_wf (a b : PubKey) (ha : a.bytes.size ≤ 75) (hb : b.bytes.size ≤ 75) :
    ProgWF (fundingProg a b) := by
  simp [ProgWF, StmtWF, InstrWF, fundingProg, ha, hb]

theorem toLocalProg_wf (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size ≤ 75) (hd : delayedPaymentKey.bytes.size ≤ 75) :
    ProgWF (toLocalProg revocationKey delayedPaymentKey csv) := by
  simp [ProgWF, StmtWF, InstrWF, toLocalProg, delayBytes, toLocalDelayBytes_size, hr, hd]

theorem fundingOps_wf (a b : PubKey) (ha : a.bytes.size = 33) (hb : b.bytes.size = 33) :
    (∀ o ∈ fundingOps a b, opcodeWF o) ∧
      (∀ o ∈ fundingOps a b, (serializeOpcode o)[0]!.toNat = wireOfAst o) := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp [fundingOps] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; rw [ha]
      unfold Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE; omega
    · simp only [opcodeWF]; rw [hb]
      unfold Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE; omega
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; decide
  · intro o ho
    simp [fundingOps] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact firstByte_pushNum_two
    · exact firstByte_pushBytes_small _ (by omega) (by omega)
    · exact firstByte_pushBytes_small _ (by omega) (by omega)
    · exact firstByte_pushNum_two
    · exact firstByte_op _

theorem toLocalOps_wf (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33) :
    (∀ o ∈ toLocalOps revocationKey delayedPaymentKey csv, opcodeWF o) ∧
      (∀ o ∈ toLocalOps revocationKey delayedPaymentKey csv,
        (serializeOpcode o)[0]!.toNat = wireOfAst o) := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp [toLocalOps] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; rw [hr]
      unfold Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE; omega
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; rw [toLocalDelayBytes_size]
      unfold Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE; omega
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; rw [hd]
      unfold Bitcoin.Script.Parser.MAX_SCRIPT_ELEMENT_SIZE; omega
    · simp only [opcodeWF]; decide
    · simp only [opcodeWF]; decide
  · intro o ho
    simp [toLocalOps] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact firstByte_op _
    · exact firstByte_pushBytes_small _ (by omega) (by omega)
    · exact firstByte_op _
    · exact firstByte_pushBytes_small _ (by rw [toLocalDelayBytes_size]; decide) (by rw [toLocalDelayBytes_size]; decide)
    · exact firstByte_op _
    · exact firstByte_op _
    · exact firstByte_pushBytes_small _ (by omega) (by omega)
    · exact firstByte_op _
    · exact firstByte_op _

theorem funding_serialize_eq (a b : PubKey) (ha : a.bytes.size ≤ 75) (hb : b.bytes.size ≤ 75) :
    serializeStmts (fundingProg a b) = serializeOpcodes (fundingOps a b) := by
  rw [serializeStmts_eq_list _ (fundingProg_wf a b ha hb), stmtListToOps_funding]

theorem toLocal_serialize_eq (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size ≤ 75) (hd : delayedPaymentKey.bytes.size ≤ 75) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv) := by
  rw [serializeStmts_eq_list _ (toLocalProg_wf revocationKey delayedPaymentKey csv hr hd),
    stmtListToOps_toLocal]

/-! ## 4. Exact wire-op lists and parse results -/

/-- The funding script's five vendor wire ops with their exact offsets. -/
def fundingWireOps (a b : PubKey) : List WireOp :=
  [ { ast := Opcode.pushNum 2, wire := 0x52, next := 1 },
    { ast := Opcode.pushBytes a.bytes, wire := 33, next := 35 },
    { ast := Opcode.pushBytes b.bytes, wire := 33, next := 69 },
    { ast := Opcode.pushNum 2, wire := 0x52, next := 70 },
    { ast := Opcode.op ⟨0xae, by decide⟩, wire := 0xae, next := 71 } ]

/-- The `to_local` script's nine vendor wire ops with their exact offsets. -/
def toLocalWireOps (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) : List WireOp :=
  [ { ast := Opcode.op ⟨0x63, by decide⟩, wire := 0x63, next := 1 },
    { ast := Opcode.pushBytes revocationKey.bytes, wire := 33, next := 35 },
    { ast := Opcode.op ⟨0x67, by decide⟩, wire := 0x67, next := 36 },
    { ast := Opcode.pushBytes (delayBytes csv), wire := 2, next := 39 },
    { ast := Opcode.op ⟨0xb2, by decide⟩, wire := 0xb2, next := 40 },
    { ast := Opcode.op ⟨0x75, by decide⟩, wire := 0x75, next := 41 },
    { ast := Opcode.pushBytes delayedPaymentKey.bytes, wire := 33, next := 75 },
    { ast := Opcode.op ⟨0x68, by decide⟩, wire := 0x68, next := 76 },
    { ast := Opcode.op ⟨0xac, by decide⟩, wire := 0xac, next := 77 } ]

theorem wireOpsFrom_fundingOps (a b : PubKey) (ha : a.bytes.size = 33) (hb : b.bytes.size = 33) :
    wireOpsFrom 0 (fundingOps a b) = fundingWireOps a b := by
  simp [wireOpsFrom, fundingOps, fundingWireOps, serializeOpcode, pushBytesWire,
    lenBytes, wireOfAst, ha, hb]
  rfl

theorem wireOpsFrom_toLocalOps (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33) :
    wireOpsFrom 0 (toLocalOps revocationKey delayedPaymentKey csv) =
      toLocalWireOps revocationKey delayedPaymentKey csv := by
  simp [wireOpsFrom, toLocalOps, toLocalWireOps, serializeOpcode, pushBytesWire,
    lenBytes, wireOfAst, delayBytes, delayBytes_size, toLocalDelayBytes, hr, hd]
  decide

theorem funding_parseWire (a b : PubKey) (ha : a.bytes.size = 33) (hb : b.bytes.size = 33) :
    parseWire (serializeOpcodes (fundingOps a b)) = some (fundingWireOps a b) := by
  rw [parseWire_serializeOpcodes _ (fundingOps_wf a b ha hb).1 (fundingOps_wf a b ha hb).2,
    wireOpsFrom_fundingOps a b ha hb]

theorem toLocal_parseWire (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33) :
    parseWire (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) =
      some (toLocalWireOps revocationKey delayedPaymentKey csv) := by
  rw [parseWire_serializeOpcodes _
      (toLocalOps_wf revocationKey delayedPaymentKey csv hr hd).1
      (toLocalOps_wf revocationKey delayedPaymentKey csv hr hd).2,
    wireOpsFrom_toLocalOps revocationKey delayedPaymentKey csv hr hd]

/-! ## 5. Vendor script-number and CHECKMULTISIG steps -/

theorem empty_push_mk (x : UInt8) : ByteArray.empty.push x = ByteArray.mk #[x] := rfl

theorem encodeScriptNum_two :
    Bitcoin.Numeric.encodeScriptNum 2 false = ByteArray.mk #[0x02] := by decide

theorem decodeNum_two :
    decodeNum ({} : PolicyFlags) (ByteArray.mk #[0x02]) 4 = .ok 2 := by
  have hd : ({} : PolicyFlags).minimalData = false := by decide
  have hbe : Bitcoin.Numeric.decodeBE false 4
      ((Bitcoin.Numeric.bytesOf (ByteArray.mk #[0x02])).reverse) =
      some (Bitcoin.Numeric.setVchBE ((Bitcoin.Numeric.bytesOf (ByteArray.mk #[0x02])).reverse)) :=
    Bitcoin.Numeric.decodeBE_some (by decide) (Or.inl rfl)
  rw [decodeNum, Bitcoin.Numeric.decodeScriptNum, hd, hbe]
  rw [Except.ok.injEq]
  decide

/-- Full vendor `OP_CHECKMULTISIG` step for the funding stack.  The two
signature checks are the only cryptographic hypotheses; everything else
(`cmsLoop`, `cmsCleanup`, encoding checks, script-number decoding) is
computed by the vendored interpreter. -/
theorem checkMultiSig_two_of_two (chk : ScriptChecker) (scriptCode a b s1 s2 dummy : ByteArray)
    (h1 : chk.base.checkECDSASignature s1 a scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    stepBody.checkMultiSig
      { flags := ({} : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0, bytes := scriptCode,
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      0xae
      { stack := [ByteArray.mk #[0x02], b, a, ByteArray.mk #[0x02], s2, s1, dummy],
        alt := [], vf := [], opCount := 1, codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 3,
          codeSep := 0, vwLeft := none } := by
  simp [empty_push_mk, stepBody.checkMultiSig, cmsLoop, cmsCleanup, checkSigEncoding,
    checkPubKeyEncoding, topAt, h1, h2, decodeNum_two,
    MAX_PUBKEYS_PER_MULTISIG, MAX_OPS_PER_SCRIPT, List.range_succ,
    pushBoolV, vchTrue, serU8]

/-! ## 6. Vendor evaluation of the funding script -/

theorem evalFrom_fundingWireOps (chk : ScriptChecker) (scriptCode : ByteArray)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (h1 : chk.base.checkECDSASignature s1 a.bytes scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := ({} : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0, bytes := scriptCode,
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      6 (fundingWireOps a b)
      { stack := [s2, s1, dummy], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 3,
          codeSep := 0, vwLeft := none } := by
  simp [fundingWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    checkMultiSig_two_of_two, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, encodeScriptNum_two,
    checkSigEncoding, checkPubKeyEncoding, decodeNum_two, empty_push_mk,
    pushBoolV, vchTrue, serU8, MAX_PUBKEYS_PER_MULTISIG, MAX_OPS_PER_SCRIPT,
    MAX_STACK_SIZE, List.range_succ, ha, hb, h1, h2]

theorem evalScriptBytes_funding (chk : ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 6 ({} : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (fundingOps a b)) [s2, s1, dummy] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (fundingOps a b)).size = 71 := by
    simp [fundingOps, serializeOpcodes, serializeOpcode, pushBytesWire, lenBytes,
      ha, hb]
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [funding_parseWire a b ha hb]
  simp [finalStack, evalFrom_fundingWireOps chk _ a b s1 s2 dummy ha hb h1 h2]


/-! ## 7. `executeWitnessScript` and the P2WSH branch of `verifyWitnessProgram` -/

theorem byteArray_beq_self (b : ByteArray) : (b == b) = true := by
  show ByteArray.beq b b = true
  cases b with
  | mk data => simp [ByteArray.beq]

theorem byteArray_bne_self (b : ByteArray) : (b != b) = false := by
  simp [bne, byteArray_beq_self]

theorem executeWitnessScript_funding (chk : ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (vwSer : Int)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 6 [dummy, s1, s2] vwSer
      (serializeOpcodes (fundingOps a b)) ({} : ScriptFlags) ({} : PolicyFlags)
      chk .witnessV0 = .ok := by
  have hs1' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < s1.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hs2' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < s2.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hdu' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < dummy.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  simp [executeWitnessScript, executeWitnessScript.runExec, evalScriptBytes_funding chk a b s1 s2 dummy ha hb h1 h2,
    hs1', hs2', hdu', Bitcoin.Numeric.castToBool]
  decide

theorem verifyWitnessProgram_funding (chk : ScriptChecker)
    (a b : PubKey) (s1 s2 dummy : ByteArray) (program : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256 (serializeOpcodes (fundingOps a b)) = program)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 6
      [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0 program
      ({} : ScriptFlags) ({} : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_funding chk a b s1 s2 dummy
      (witnessSerSize [dummy, s1, s2, serializeOpcodes (fundingOps a b)]) ha hb hs1 hs2 hdu h1 h2]

/-! ## 8. Model-side instantiation and the agreement statement -/

theorem wordBEEmit_size (x : UInt32) : (wordBEEmit x).size = 4 := by
  simp [wordBEEmit, List.size_toByteArray]

theorem foldl_word_size (n : Nat) (f : Nat → UInt32) :
    ((List.range n).foldl (fun acc i => acc ++ wordBEEmit (f i)) ByteArray.empty).size =
      4 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp [ih, wordBEEmit_size, Nat.mul_succ]

theorem hashSha256_size (x : ByteArray) : (hashSha256 x).size = 32 := by
  simp [hashSha256, foldl_word_size]

/-- The model's signature law instantiated with the vendored checker at a
fixed script code.  BIP 143 sighash construction stays inside the vendor
checker; the model's `msg` parameter is therefore unused by this
instantiation.  `csvOk`/`cltvOk` are `true` here because the funding
program uses neither; the `to_local` CSV boundary is discussed below. -/
def vendorLaws (chk : ScriptChecker) (scriptCode : ByteArray) : InterpreterLaws where
  sigCheck := fun pk _msg sig =>
    chk.base.checkECDSASignature sig pk scriptCode .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
  csvOk := fun _ => true
  cltvOk := fun _ => true
  sha256 := hashSha256
  hash160 := hashRipemd160

/-- The same instantiation, with the model's `csvOk` tied to the vendored
sequence check for one already-decoded `to_self_delay` value.  This is the
law used for the delayed `to_local` agreement: the model and the vendor
machine consult the *same* `checkSequenceDef chk.env n`. -/
def vendorLawsCSV (chk : ScriptChecker) (scriptCode : ByteArray)
    (n : Bitcoin.Numeric.ScriptNum) : InterpreterLaws :=
  { vendorLaws chk scriptCode with
    csvOk := fun _ => checkSequenceDef chk.env n }

theorem funding_model_spend (chk : ScriptChecker) (msg : ByteArray)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    P2WSHSpend (vendorLaws chk (serializeOpcodes (fundingOps a b))) msg
      (hashSha256 (serializeOpcodes (fundingOps a b)))
      (serializeOpcodes (fundingOps a b)) (fundingProg a b) [s2, s1, dummy] := by
  have hsp := fundingOutput_spendable (vendorLaws chk (serializeOpcodes (fundingOps a b)))
    msg a b dummy s1 s2 h1 h2
  have hser : TwoOfTwoScriptBytes a b = serializeOpcodes (fundingOps a b) := by
    rw [← fundingProg_serialize a b]
    exact funding_serialize_eq a b (by omega) (by omega)
  simpa [vendorLaws, hser] using hsp

/-- **Funding agreement.**  The real vendored P2WSH verifier returns `.ok`
on the BOLT 3 funding witness exactly when the wave-4 model's `P2WSHSpend`
holds, under the same two vendored ECDSA checker calls.  This is the
consensus-facing bridge for the funding output. -/
theorem funding_interpreters_agree (chk : ScriptChecker) (msg : ByteArray)
    (a b : PubKey) (s1 s2 dummy : ByteArray)
    (ha : a.bytes.size = 33) (hb : b.bytes.size = 33)
    (hs1 : s1.size ≤ 520) (hs2 : s2.size ≤ 520) (hdu : dummy.size ≤ 520)
    (h1 : chk.base.checkECDSASignature s1 a.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (h2 : chk.base.checkECDSASignature s2 b.bytes
      (serializeOpcodes (fundingOps a b)) .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 6
        [dummy, s1, s2, serializeOpcodes (fundingOps a b)] 0
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        ({} : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLaws chk (serializeOpcodes (fundingOps a b))) msg
        (hashSha256 (serializeOpcodes (fundingOps a b)))
        (serializeOpcodes (fundingOps a b)) (fundingProg a b) [s2, s1, dummy] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_funding chk a b s1 s2 dummy
      (hashSha256 (serializeOpcodes (fundingOps a b))) ha hb hs1 hs2 hdu
      (hashSha256_size _) rfl h1 h2
  · exact funding_model_spend chk msg a b s1 s2 dummy ha hb h1 h2

/-! ## 9. Vendor evaluation of the delayed `to_local` branch -/

theorem serializeOpcodes_toLocal_size (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) (hr : revocationKey.bytes.size = 33)
    (hd : delayedPaymentKey.bytes.size = 33) :
    (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 := by
  simp [toLocalOps, serializeOpcodes, serializeOpcode, pushBytesWire, lenBytes,
    delayBytes, toLocalDelayBytes_size, hr, hd]

/-- Vendor `evalFrom` computation for the `OP_ELSE` (delayed) branch of
`to_local`.  The witness supplies an empty selector and a signature, so the
machine starts with the empty selector on top.  The sequence-number decode,
the disable-flag skip, the `OP_CSV` law and the delayed-key signature check
are the only non-computational inputs; all control flow, stack movement and
opcode counting is done by the vendored step function. -/
theorem evalFrom_toLocalWireOps_delayed (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalFrom
      { flags := ({ csv := true } : ScriptFlags), pol := ({} : PolicyFlags), chk := chk,
        sv := .witnessV0,
        bytes := serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv),
        ed := (default : Bitcoin.Crypto.Seam.ScriptExecutionData) }
      10 (toLocalWireOps revocationKey delayedPaymentKey csv)
      { stack := [ByteArray.empty, sig], alt := [], vf := [], opCount := 0,
        codeSep := 0, vwLeft := none }
    = Except.ok
        { stack := [ByteArray.mk #[0x01]], alt := [], vf := [], opCount := 6,
          codeSep := 0, vwLeft := none } := by
  simp [toLocalWireOps, evalFrom, stepChecked, stepBody, stepBody.dispatchOp,
    evalChecksigDispatch, evalChecksigPreTapscript, checkSigEncoding, checkPubKeyEncoding,
    Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList,
    Bitcoin.Numeric.bytesOf, delayBytes, topAt, pushBoolV, vchTrue, serU8, disabledWire,
    Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE, MAX_STACK_SIZE, MAX_OPS_PER_SCRIPT,
    toLocalDelayBytes_size, hdis, hseq, hsig, hr, hd]
  rw [show decodeNum ({} : PolicyFlags) (toLocalDelayBytes csv) 5 = .ok n by
    simpa [delayBytes] using hdec]
  have hnlt : ¬ n < 0 := Int.not_lt.mpr hnn
  simp [hnlt, hdis, hseq, hsig, Bitcoin.Numeric.castToBoolList, empty_push_eq]
  rfl

theorem evalScriptBytes_toLocal_delayed (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    evalScriptBytes 10 ({ csv := true } : ScriptFlags) ({} : PolicyFlags)
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      [ByteArray.empty, sig] chk .witnessV0
      (default : Bitcoin.Crypto.Seam.ScriptExecutionData)
    = Except.ok [ByteArray.mk #[0x01]] := by
  unfold evalScriptBytes
  have hsz : (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)).size = 77 :=
    serializeOpcodes_toLocal_size revocationKey delayedPaymentKey csv hr hd
  rw [if_neg (by simp [hsz, MAX_SCRIPT_SIZE])]
  rw [toLocal_parseWire revocationKey delayedPaymentKey csv hr hd]
  simp [finalStack,
    evalFrom_toLocalWireOps_delayed chk revocationKey delayedPaymentKey csv sig n
      hr hd hdec hnn hdis hseq hsig]

theorem executeWitnessScript_toLocal_delayed (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (vwSer : Int)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    executeWitnessScript 10 [sig, ByteArray.empty] vwSer
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk .witnessV0 = .ok := by
  have hsig' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < sig.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; omega
  have hempty' : ¬ Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE < ByteArray.empty.size := by
    unfold Bitcoin.Interpreter.MAX_SCRIPT_ELEMENT_SIZE; decide
  simp [executeWitnessScript, executeWitnessScript.runExec,
    evalScriptBytes_toLocal_delayed chk revocationKey delayedPaymentKey csv sig n
      hr hd hdec hnn hdis hseq hsig,
    hsig', hempty', Bitcoin.Numeric.castToBool, Bitcoin.Numeric.castToBoolList]
  decide

theorem verifyWitnessProgram_toLocal_delayed (chk : ScriptChecker)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok := by
  simp [verifyWitnessProgram, hps, hprog, byteArray_bne_self,
    executeWitnessScript_toLocal_delayed chk revocationKey delayedPaymentKey csv sig n
      (witnessSerSize [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)])
      hr hd hsigsz hdec hnn hdis hseq hsig]

/-! ### Model-side delayed branch and agreement -/

theorem toLocal_model_spend_delayed (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    P2WSHSpend (vendorLawsCSV chk
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
      msg
      (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  have hcsv : (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n).csvOk
      (delayBytes csv) = true := by
    simpa [vendorLawsCSV, vendorLaws] using hseq
  have hsig' : (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n).sigCheck
      delayedPaymentKey.bytes msg sig = true := by
    simpa [vendorLawsCSV, vendorLaws] using hsig
  have hsp := toLocalOutput_delayed_spendable
    (vendorLawsCSV chk
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
    msg revocationKey delayedPaymentKey csv sig hcsv hsig'
  have hbytes : (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes =
      serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv) := by
    rw [← toLocalProg_serialize revocationKey delayedPaymentKey csv,
      toLocal_serialize_eq revocationKey delayedPaymentKey csv (by omega) (by omega)]
  simpa [vendorLawsCSV, vendorLaws, hbytes] using hsp

/-- **Delayed `to_local` agreement (positive direction).**  On the
`OP_ELSE` branch, the real vendored P2WSH verifier returns `.ok` under the
same hypotheses that establish the wave-4 model's `P2WSHSpend` with the
sequence law `vendorLawsCSV`.  The shared
inputs are the decoded delay `n`, its non-negativity and disable-bit
conditions, the vendored `checkSequenceDef`, and the delayed-key ECDSA
check.  This is the narrowed consensus boundary: BIP 143 sighash and
sequence-env construction remain caller obligations. -/
theorem toLocal_delayed_interpreters_agree (chk : ScriptChecker) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (n : Bitcoin.Numeric.ScriptNum)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hdec : decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok n)
    (hnn : 0 ≤ n)
    (hdis : Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0)
    (hseq : checkSequenceDef chk.env n = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :
    verifyWitnessProgram 10
        [sig, ByteArray.empty,
          serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)]
        0
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
      P2WSHSpend (vendorLawsCSV chk
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)) n)
        msg
        (hashSha256 (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv)))
        (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey csv))
        (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] := by
  refine ⟨?_, ?_⟩
  · exact verifyWitnessProgram_toLocal_delayed chk revocationKey delayedPaymentKey csv
      sig n _ hr hd hsigsz hdec hnn hdis hseq hsig (hashSha256_size _) rfl
  · exact toLocal_model_spend_delayed chk msg revocationKey delayedPaymentKey csv
      sig n hr hd hdec hnn hdis hseq hsig

end LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
