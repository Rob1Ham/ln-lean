import Bitcoin.Data.Basic
import Bitcoin.Data.Script
import Bitcoin.Data.Tx
import LnLean.Basic.Core
import LnLean.Bitcoin.Seam
import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Proofs.Bitcoin.FundingScriptTargets
import LnLean.Proofs.Bitcoin.ToLocalScriptTargets

/-!
# Spending bridges for P2WSH funding and `to_local` outputs

**English claim.**  This module supplies the first *execution-level* bridge for
the two L1 scripts the Lightning model builds:

* the BOLT 3 funding output `OP_0 <0x20> SHA256(OP_2 <pk1> <pk2> OP_2
  OP_CHECKMULTISIG)`, spendable by a witness that reveals the 2-of-2 witness
  script and carries a valid signature from each funding key; and
* the BOLT 3 `to_local` output `OP_0 <0x20> SHA256(OP_IF <revocationpubkey>
  OP_ELSE <to_self_delay> OP_CSV OP_DROP <local_delayedpubkey> OP_ENDIF
  OP_CHECKSIG)`, spendable through **either** the revocation branch (selector
  `0x01`, no CSV condition) **or** the delayed branch (selector `empty`, CSV
  condition satisfied, `local_delayedpubkey` signature).

The semantics is *explicit and local to this module*: a small stack machine
over an opcode AST (`Instr` / `Stmt`), a serializer proved equal to the seam's
byte templates, and an `InterpreterLaws` record naming the four pieces of
Bitcoin semantics this tree does not model:

* `sigCheck` — the signature/sighash law (assumption C3; the BIP 143 sighash
  itself is not computed),
* `csvOk` — `OP_CHECKSEQUENCEVERIFY` (BIP 112) against the spending input,
* `cltvOk` — `OP_CHECKLOCKTIMEVERIFY` (BIP 65) against the spending input,
* `sha256` / `hash160` — the hash floor (C1/C2).

Every theorem below is conditional on those laws at the point of use.  No
theorem claims Bitcoin consensus acceptance: the vendored
`Bitcoin.Interpreter.verifyScript` (a real, fuel-bounded transliteration of
Core's `VerifyScript`, `vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean`)
is **not** connected here.  It is reachable only through
`ConsensusSpendBridge`, an explicit unproved `Prop` hypothesis.  The final
section mechanizes the limits: the model's truthiness is not Core's
`cast_to_bool`, `OP_CHECKMULTISIG` is the 2-of-2 instantiation only, and the
byte-level decoder is not modelled (the link runs through the serializer).

## What is proved, not assumed

* The script bytes equal the serialization of the executed program
  (`fundingProg_serialize`, `toLocalProg_serialize`).
* The funding program is the BOLT 3 2-of-2 script over the ordered funding
  keys (`fundingProg_serialize_params`), and the `to_local` program serializes
  to the full two-branch template (`toLocalProg_serialize_template`).
* Branch selection: the revocation branch ignores the CSV condition, the
  delayed branch requires it, an empty witness fails, and a wrong signature
  produces `false` rather than acceptance.

## Anchors

* BOLT 3 §Funding Transaction Output (`refs/bolts/03-transactions.md:75-83`)
  and §`to_local` Output (`:113-135`).
* BIP 141 (P2WSH), BIP 143 (sighash), BIP 65 (`OP_CLTV`), BIP 112
  (`OP_CSV`), BIP 147 (NULLDUMMY).
* `refs/rust-lightning/lightning/src/ln/chan_utils.rs:847-866`
  (`make_funding_redeemscript`) and `:687-700`
  (`get_revokeable_redeemscript`).
-/

namespace LnLean.Proofs.Bitcoin.SpendTargets

set_option autoImplicit false

open Bitcoin.Data
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.FundingScriptTargets

/-! ## A minimal stack machine -/

/-- The witness / script machine stack.  Head = top of stack, matching the
vendored interpreter's `Bitcoin.Interpreter.Stack`. -/
abbrev Stack := List ByteArray

/-- Canonical `true` pushed by a satisfied signature/timelock check. -/
def oneByte : ByteArray := ByteArray.empty.push 1

/-- Canonical `false`, encoded as the empty stack element (Core's
`CScriptNum(0)`). -/
def zeroByte : ByteArray := ByteArray.empty

/-- Model truthiness: a non-empty stack element is true.

This is *not* Core's `cast_to_bool`: Core also rejects negative zero and any
all-zero encoding.  The simplification is exact for the canonical `0x01` and
empty selectors this module executes, and `truthy_nonminimal_true` below
records the divergence as a limitation. -/
def truthy (d : ByteArray) : Bool := d.size != 0

@[simp] theorem truthy_oneByte : truthy oneByte = true := rfl

@[simp] theorem truthy_zeroByte : truthy zeroByte = false := rfl

/-- `bool` → the canonical stack element. -/
def boolBytes (b : Bool) : ByteArray := if b then oneByte else zeroByte

@[simp] theorem boolBytes_true : boolBytes true = oneByte := rfl

@[simp] theorem boolBytes_false : boolBytes false = zeroByte := rfl

/-- The pieces of Bitcoin script semantics that the tree does not model.
They are explicit fields so every theorem that consumes them names them.

* `sigCheck pk msg sig` is the signature law: `true` iff `sig` is a valid
  signature by `pk` over the sighash `msg`.  The BIP 143 sighash computation
  is *not* modelled; `msg` is supplied by the caller.
* `csvOk d` is `OP_CHECKSEQUENCEVERIFY` applied to the raw two-byte delay
  element `d` (`Bitcoin.Numeric` decoding is not modelled).
* `cltvOk d` is `OP_CHECKLOCKTIMEVERIFY`.
* `sha256` / `hash160` are the hash floor. -/
structure InterpreterLaws where
  sigCheck : ByteArray → ByteArray → ByteArray → Bool
  csvOk : ByteArray → Bool
  cltvOk : ByteArray → Bool
  sha256 : ByteArray → ByteArray
  hash160 : ByteArray → ByteArray

/-- The opcodes used by the funding and `to_local` templates.  `num n` is an
`OP_1`..`OP_16` script-number push. -/
inductive Instr where
  | push (d : ByteArray)
  | num (n : Nat)
  | dup
  | drop
  | hash160
  | sha256
  | equal
  | equalVerify
  | checkSig
  | checkMultiSig
  | csv
  | cltv
deriving Repr, DecidableEq, BEq

/-- A structured program: basic instructions and one-level
`OP_IF ... OP_ELSE ... OP_ENDIF` blocks.  Nested conditionals are not
representable; the funding and `to_local` templates do not need them.
(`offeredHtlcWitnessScript` / `receivedHtlcWitnessScript` do, and are out of
scope for this module.) -/
inductive Stmt where
  | basic (i : Instr)
  | ite (t e : List Stmt)
deriving Repr

mutual
/-- Serialize one instruction.  This runs from program to bytes: the seam
defines the bytes, and the theorems below identify them with the serialization
of the program executed by this module. -/
def Instr.serialize : Instr → ByteArray
  | .push d => pushData d
  | .num n => ByteArray.empty.push (0x50 + n).toUInt8
  | .dup => ByteArray.empty.push 0x76
  | .drop => ByteArray.empty.push 0x75
  | .hash160 => ByteArray.empty.push 0xa9
  | .sha256 => ByteArray.empty.push 0xa8
  | .equal => ByteArray.empty.push 0x87
  | .equalVerify => ByteArray.empty.push 0x88
  | .checkSig => ByteArray.empty.push 0xac
  | .checkMultiSig => ByteArray.empty.push 0xae
  | .csv => ByteArray.empty.push 0xb2
  | .cltv => ByteArray.empty.push 0xb1

def Stmt.serialize : Stmt → ByteArray
  | .basic i => i.serialize
  | .ite t e =>
      (ByteArray.empty.push 0x63) ++ serializeStmts t ++
        (ByteArray.empty.push 0x67) ++ serializeStmts e ++
        (ByteArray.empty.push 0x68)

def serializeStmts (prog : List Stmt) : ByteArray :=
  prog.foldl (fun acc s => acc ++ s.serialize) ByteArray.empty
end

/-- `OP_2` as a stack element (`CScriptNum(2)`). -/
def twoByte : ByteArray := ByteArray.mk #[0x02]

/-- Recognise the `OP_2` count pushed by the BOLT 3 funding script.  A
`ByteArray` equality test is avoided so the definition reduces on concrete
scripts without needing `DecidableEq` in the kernel. -/
def isOp2 (d : ByteArray) : Bool := d.size = 1 && (d.get! 0 == 0x02)

@[simp] theorem isOp2_twoByte : isOp2 (ByteArray.mk #[0x02]) = true := rfl

@[simp] theorem isOp2_three : isOp2 (ByteArray.mk #[0x03]) = false := rfl

/-- One machine step.  `none` is a script failure (the interpreter's
`ScriptError`); a `Bool` result is pushed as `oneByte`/`zeroByte`. -/
def step (L : InterpreterLaws) (msg : ByteArray) : Instr → Stack → Option Stack
  | .push d, st => some (d :: st)
  | .num n, st => some (ByteArray.mk #[n.toUInt8] :: st)
  | .dup, st =>
      match st with
      | [] => none
      | d :: rest => some (d :: d :: rest)
  | .drop, st =>
      match st with
      | [] => none
      | _ :: rest => some rest
  | .hash160, st =>
      match st with
      | [] => none
      | d :: rest => some (L.hash160 d :: rest)
  | .sha256, st =>
      match st with
      | [] => none
      | d :: rest => some (L.sha256 d :: rest)
  | .equal, st =>
      match st with
      | a :: b :: rest => some (boolBytes (bytesBEq a b) :: rest)
      | _ => none
  | .equalVerify, st =>
      match st with
      | a :: b :: rest => if bytesBEq a b then some rest else none
      | _ => none
  | .checkSig, st =>
      match st with
      | pk :: sig :: rest => some (boolBytes (L.sigCheck pk msg sig) :: rest)
      | _ => none
  | .checkMultiSig, st =>
      -- BOLT 3 pushes `<2> <pk1> <pk2> <2>`; with witness
      -- `[dummy, sig1, sig2]` (dummy at the bottom, so the machine stack is
      -- `[sig2, sig1, dummy]`) the top-down stack is
      -- `<2> pk2 pk1 <2> sig2 sig1 dummy`.
      match st with
      | n :: pkB :: pkA :: m :: sB :: sA :: _dummy :: rest =>
          if isOp2 n && isOp2 m then
            some (boolBytes (L.sigCheck pkA msg sA && L.sigCheck pkB msg sB) :: rest)
          else none
      | _ => none
  | .csv, st =>
      -- BIP 112: the delay element is inspected and left on the stack.
      match st with
      | d :: rest => if L.csvOk d then some (d :: rest) else none
      | _ => none
  | .cltv, st =>
      -- BIP 65: the locktime element is inspected and left on the stack.
      match st with
      | d :: rest => if L.cltvOk d then some (d :: rest) else none
      | _ => none

mutual
/-- Execute one structured statement. -/
def execStmt (L : InterpreterLaws) (msg : ByteArray) : Stmt → Stack → Option Stack
  | .basic i, st => step L msg i st
  | .ite t e, st =>
      match st with
      | [] => none
      | v :: st' =>
          if truthy v then execStmts L msg t st' else execStmts L msg e st'

/-- Execute a structured program. -/
def execStmts (L : InterpreterLaws) (msg : ByteArray) : List Stmt → Stack → Option Stack
  | [], st => some st
  | s :: rest, st => (execStmt L msg s st).bind (execStmts L msg rest)
end

/-- Acceptance: the script leaves exactly the canonical `true` on a clean
stack (P2WSH applies `CLEANSTACK`). -/
def Accepts (L : InterpreterLaws) (msg : ByteArray) (prog : List Stmt)
    (st : Stack) : Prop :=
  execStmts L msg prog st = some [oneByte]

/-- A complete P2WSH spend: the revealed witness script is the serialization
of `prog`, its SHA-256 is the committed program, and running `prog` on the
machine stack accepts.  `st` is in machine order (head = top); the witness
order is `st.reverse ++ [witnessScript]`, as in `SpendableOutput`. -/
def P2WSHSpend (L : InterpreterLaws) (msg : ByteArray)
    (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack) : Prop :=
  serializeStmts prog = witnessScript ∧
    L.sha256 witnessScript = program ∧
    Accepts L msg prog st

/-- An output-level spend: a P2WSH `scriptPubKey`, the revealed witness
script last in the witness stack, and a `P2WSHSpend` for the execution part. -/
def SpendableOutput (L : InterpreterLaws) (msg : ByteArray)
    (spk : Bitcoin.Data.Script) (witness : Bitcoin.Data.WitnessStack) : Prop :=
  ∃ (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack),
    spk = p2wsh program ∧
      witness = st.reverse ++ [witnessScript] ∧
      P2WSHSpend L msg program witnessScript prog st

/-! ## The BOLT 3 programs -/

/-- The two-byte little-endian `to_self_delay` stack element. -/
def delayBytes (csv : Blocks) : ByteArray := toLocalDelayBytes csv

@[simp] theorem delayBytes_eq (csv : Blocks) :
    delayBytes csv = toLocalDelayBytes csv := rfl

@[simp] theorem delayBytes_size (csv : Blocks) :
    (delayBytes csv).size = 2 :=
  toLocalDelayBytes_size csv

/-- `OP_2 <pk1> <pk2> OP_2 OP_CHECKMULTISIG`. -/
def fundingProg (a b : PubKey) : List Stmt :=
  [ .basic (.num 2),
    .basic (.push a.bytes),
    .basic (.push b.bytes),
    .basic (.num 2),
    .basic .checkMultiSig ]

/-- `OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
<local_delayedpubkey> OP_ENDIF OP_CHECKSIG`. -/
def toLocalProg (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    List Stmt :=
  [ .ite [ .basic (.push revocationKey.bytes) ]
         [ .basic (.push (delayBytes csv)),
           .basic .csv,
           .basic .drop,
           .basic (.push delayedPaymentKey.bytes) ],
    .basic .checkSig ]

/-! ## Byte-level agreement with the seam -/

/-- The funding program serializes to the exact BOLT 3 2-of-2 witness-script
bytes. -/
theorem fundingProg_serialize (a b : PubKey) :
    serializeStmts (fundingProg a b) = TwoOfTwoScriptBytes a b := by
  simp [fundingProg, serializeStmts, Stmt.serialize, Instr.serialize,
    TwoOfTwoScriptBytes, pushData, OP_CHECKMULTISIG]

/-- The funding program serializes to `FundingParams.witnessScript` for the
ordered funding keys. -/
theorem fundingProg_serialize_params (p : FundingParams) :
    serializeStmts
        (fundingProg (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1
          (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2) =
      p.witnessScript.bytes := by
  rw [fundingProg_serialize]
  exact (witnessScript_eq_TwoOfTwoScriptBytes p).symm

/-- The `to_local` program serializes to the full two-branch seam script. -/
theorem toLocalProg_serialize (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes := by
  simp [toLocalProg, serializeStmts, Stmt.serialize, Instr.serialize,
    toLocalScriptFull, toLocalDelayPush_eq_pushData_delayBytes, delayBytes,
    toLocalDelayBytes, pushData, OP_IF, OP_ELSE, OP_CSV, OP_DROP, OP_ENDIF,
    OP_CHECKSIG, ByteArray.append_assoc]

/-- The `to_local` program serializes to the `ScriptTemplates` BOLT 3
template. -/
theorem toLocalProg_serialize_template (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      (toLocalWitnessScript revocationKey delayedPaymentKey csv).bytes := by
  rw [toLocalProg_serialize,
    LnLean.Proofs.Bitcoin.ToLocalScriptTargets.toLocalScriptFull_eq_template]

/-! ## Execution: funding output -/

/-- **2-of-2 funding spend, execution level.**  If both ordered funding keys
verify their signatures over `msg`, the BOLT 3 2-of-2 program accepts the
machine stack `[sig2, sig1, dummy]` (i.e. the BOLT witness `[dummy, sig1,
sig2]` read bottom-to-top), leaving the canonical `true` on a clean stack. -/
theorem exec_funding (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [oneByte] := by
  simp [fundingProg, execStmts, execStmt, step, h1, h2]

/-- A single signature does not spend the 2-of-2 funding output: the
interpreter pushes `false`, so the final stack is not `[true]`. -/
theorem exec_funding_one_signature (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = false) :
    execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [zeroByte] := by
  simp [fundingProg, execStmts, execStmt, step, h1, h2]

theorem zeroByte_ne_oneByte : zeroByte ≠ oneByte := by
  decide

/-- Hence the 2-of-2 funding output is *not* accepted with only one valid
signature. -/
theorem not_accepts_funding_one_signature (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = false) :
    ¬ Accepts L msg (fundingProg a b) [s2, s1, dummy] := by
  unfold Accepts
  rw [exec_funding_one_signature L msg a b dummy s1 s2 h1 h2]
  simp [zeroByte_ne_oneByte]

/-- The BOLT witness order for the funding input: machine stack
`[sig2, sig1, dummy]` is witness `[dummy, sig1, sig2]`. -/
theorem fundingWitness_reverse (dummy s1 s2 : ByteArray) :
    ([s2, s1, dummy] : Stack).reverse = [dummy, s1, s2] := rfl

/-- **Funding output spendability.**  The P2WSH output
`OP_0 <0x20> SHA256(2-of-2 script)` is spendable with the BOLT witness
`[dummy, sig1, sig2, witnessScript]` whenever both funding keys sign.  The
hash link is the explicit equation `program = sha256(witnessScript)`; it is
not derived from `FundingParams.WellFormed` (see `L1-03`). -/
theorem fundingOutput_spendable (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    P2WSHSpend L msg (L.sha256 (TwoOfTwoScriptBytes a b))
      (TwoOfTwoScriptBytes a b) (fundingProg a b) [s2, s1, dummy] :=
  ⟨fundingProg_serialize a b, rfl,
    exec_funding L msg a b dummy s1 s2 h1 h2⟩

/-- The same statement for `FundingParams`, with the key order supplied by
`orderedFundingKeys` and the stored witness-script hash linked to the script
bytes. -/
theorem fundingParams_spendable (L : InterpreterLaws) (msg : ByteArray)
    (p : FundingParams) (dummy s1 s2 : ByteArray)
    (hlink : p.witnessScriptHash = L.sha256 p.witnessScript.bytes)
    (h1 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1.bytes msg s1 = true)
    (h2 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2.bytes msg s2 = true) :
    P2WSHSpend L msg p.witnessScriptHash p.witnessScript.bytes
      (fundingProg (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1
        (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2)
      [s2, s1, dummy] := by
  refine ⟨fundingProg_serialize_params p, ?_, ?_⟩
  · exact hlink.symm
  · exact exec_funding L msg _ _ dummy s1 s2 h1 h2

/-- **Funding output is an output-level spend, not just a script run.**  The
`scriptPubKey` is the BIP 141 P2WSH wrapper over the program's hash and the
witness ends with the revealed witness script. -/
theorem fundingOutput_spendable_output (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    SpendableOutput L msg (p2wsh (L.sha256 (TwoOfTwoScriptBytes a b)))
      ([dummy, s1, s2] ++ [TwoOfTwoScriptBytes a b]) :=
  ⟨L.sha256 (TwoOfTwoScriptBytes a b), TwoOfTwoScriptBytes a b,
    fundingProg a b, [s2, s1, dummy], rfl,
    by rw [fundingWitness_reverse],
    fundingOutput_spendable L msg a b dummy s1 s2 h1 h2⟩

/-! ## Execution: `to_local` revocation and delayed branches -/

/-- **Revocation branch.**  Selector `0x01` selects the `OP_IF` branch, which
pushes the revocation key and requires its signature.  The CSV law is *not*
consulted on this branch, so a revoked commitment can be punished before (or
after) the delay elapses. -/
theorem exec_toLocal_revocation (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [oneByte] := by
  simp [toLocalProg, execStmts, execStmt, step, h]

/-- The revocation branch is independent of the CSV condition: even when
`csvOk` fails, the revocation witness is accepted. -/
theorem exec_toLocal_revocation_independent_of_csv (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (_hcsv : L.csvOk (delayBytes csv) = false)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [oneByte] :=
  exec_toLocal_revocation L msg revocationKey delayedPaymentKey csv sig h

/-- **Delayed local-payment branch.**  Selector `empty` (false) selects the
`OP_ELSE` branch: the delay element is checked by `OP_CSV`, dropped, the
delayed key is pushed, and its signature is required. -/
theorem exec_toLocal_delayed (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [zeroByte, sig] = some [oneByte] := by
  have hcsv' : L.csvOk (toLocalDelayBytes csv) = true := by simpa using hcsv
  simp [toLocalProg, execStmts, execStmt, step, hcsv', h]

/-- The delayed branch is *unavailable* when the CSV condition fails: the
interpreter errors instead of pushing `false`, so no acceptance exists. -/
theorem exec_toLocal_delayed_csv_fails (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = false) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [zeroByte, sig] = none := by
  have hcsv' : L.csvOk (toLocalDelayBytes csv) = false := by simpa using hcsv
  simp [toLocalProg, execStmts, execStmt, step, hcsv']

/-- An empty witness cannot select either branch: `OP_IF` underflows. -/
theorem exec_toLocal_empty_witness (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv) [] = none := by
  simp [toLocalProg, execStmts, execStmt, step]

/-- A revocation-branch witness whose signature does not verify under the
revocation key is rejected (the interpreter pushes `false`). -/
theorem exec_toLocal_revocation_bad_sig (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = false) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [zeroByte] := by
  simp [toLocalProg, execStmts, execStmt, step, h]

/-- Therefore a bad revocation signature does not spend the output. -/
theorem not_accepts_toLocal_revocation_bad_sig (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = false) :
    ¬ Accepts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] := by
  unfold Accepts
  rw [exec_toLocal_revocation_bad_sig L msg revocationKey delayedPaymentKey csv sig h]
  simp [zeroByte_ne_oneByte]

/-- **`to_local` output spendability via the revocation branch.**  With the
P2WSH hash link, witness `[sig, 0x01, witnessScript]` spends the output.  No
CSV hypothesis is needed. -/
theorem toLocalOutput_revocation_spendable (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    P2WSHSpend L msg
      (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig] :=
  ⟨toLocalProg_serialize revocationKey delayedPaymentKey csv, rfl,
    exec_toLocal_revocation L msg revocationKey delayedPaymentKey csv sig h⟩

/-- **`to_local` output spendability via the delayed branch.**  With the same
hash link, witness `[sig, empty, witnessScript]` spends the output when the
CSV law holds and the delayed key signs. -/
theorem toLocalOutput_delayed_spendable (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    P2WSHSpend L msg
      (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig] :=
  ⟨toLocalProg_serialize revocationKey delayedPaymentKey csv, rfl,
    exec_toLocal_delayed L msg revocationKey delayedPaymentKey csv sig hcsv h⟩

/-- The revocation-branch spend at the output level (`scriptPubKey` and full
witness, revealed script last). -/
theorem toLocalOutput_revocation_spendable_output (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    SpendableOutput L msg
      (toLocalScriptPubKey
        (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, oneByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes]) :=
  ⟨_, _, _, _, rfl, rfl,
    toLocalOutput_revocation_spendable L msg revocationKey delayedPaymentKey csv sig h⟩

/-- The delayed-branch spend at the output level. -/
theorem toLocalOutput_delayed_spendable_output (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    SpendableOutput L msg
      (toLocalScriptPubKey
        (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, zeroByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes]) :=
  ⟨_, _, _, _, rfl, rfl,
    toLocalOutput_delayed_spendable L msg revocationKey delayedPaymentKey csv sig hcsv h⟩

/-! ## Integration with the funding- and commitment-output models -/

/-- **A confirmed funding output is spendable.**  Composing
`FundingConfirmed` (which fixes the output's `scriptPubKey`) with the 2-of-2
execution and the hash link yields the output-level spend for the confirmed
`TxOut` itself, not merely for a constructed script. -/
theorem fundingConfirmed_spendable_output
    (L : InterpreterLaws) (msg : ByteArray) (p : FundingParams)
    (tx : Bitcoin.Data.Tx) (index : Nat) (dummy s1 s2 : ByteArray)
    (hc : FundingConfirmed p tx index)
    (hlink : p.witnessScriptHash = L.sha256 p.witnessScript.bytes)
    (h1 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1.bytes msg s1 = true)
    (h2 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2.bytes msg s2 = true) :
    ∃ out : Bitcoin.Data.TxOut,
      tx.vout[index]? = some out ∧
        SpendableOutput L msg out.scriptPubKey
          ([dummy, s1, s2] ++ [p.witnessScript.bytes]) := by
  rcases hc with ⟨out, hout, _hvalue, hscript⟩
  refine ⟨out, hout, ?_⟩
  rw [hscript]
  exact ⟨_, _, _, _, rfl, by rw [fundingWitness_reverse],
    fundingParams_spendable L msg p dummy s1 s2 hlink h1 h2⟩

/-- **The `to_local` output of `commitmentOutputs` is spendable through its
delayed branch.**  The output is located by kind, its `scriptPubKey` is the
P2WSH of the stored hash, and the spend uses the full BOLT 3 two-branch
witness script.  Assumptions: the hash link, the CSV law for the stored
`to_self_delay`, and the delayed-key signature. -/
theorem commitmentOutputs_toLocal_delayed_spendable
    (L : InterpreterLaws) (msg : ByteArray) (p : CommitmentParams) (sig : ByteArray)
    (hlink : p.toLocalWitnessScriptHash =
      L.sha256 (toLocalScriptFull p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes)
    (hcsv : L.csvOk (delayBytes p.toSelfDelay) = true)
    (h : L.sigCheck p.delayedPaymentKey.bytes msg sig = true) :
    ∃ o : CommitmentOutput,
      o ∈ commitmentOutputs p ∧ o.kind = OutputKind.toLocal ∧
        SpendableOutput L msg o.scriptPubKey
          ([sig, zeroByte] ++
            [(toLocalScriptFull p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes]) := by
  refine ⟨{ kind := OutputKind.toLocal
            value := p.toLocalValue
            scriptPubKey := toLocalScriptPubKey p.toLocalWitnessScriptHash },
    ?_, rfl, ?_⟩
  · simp [commitmentOutputs]
  · rw [hlink]
    exact toLocalOutput_delayed_spendable_output L msg p.revocationKey
      p.delayedPaymentKey p.toSelfDelay sig hcsv h

/-! ## The consensus bridge (unproved, explicit) -/

/-- **Bridge obligation to an L1 verifier.**  `verify spk witness tx` is the
consensus acceptance predicate; the `↔` says it agrees with the local stack
machine for every P2WSH output whose revealed script serializes a program.
This is a `Prop`, not a postulated constant: no theorem assumes it globally, and the
composition theorems take it as an explicit hypothesis.

The vendored `Bitcoin.Interpreter.verifyScript` is the intended concrete
instantiation, but connecting it would require importing and proving over
`Bitcoin.Interpreter.Defs` (P2WSH dispatch, `OP_CHECKMULTISIG`, `OP_CSV`,
BIP 143 sighash encoding), which is outside this module. -/
def ConsensusSpendBridge
    (verify : Bitcoin.Data.Script → Bitcoin.Data.WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray) : Prop :=
  ∀ (vtx : Bitcoin.Data.Tx) (program witnessScript : ByteArray)
      (prog : List Stmt) (st : Stack),
    serializeStmts prog = witnessScript →
    (verify (p2wsh program) (st.reverse ++ [witnessScript]) vtx = true ↔
      L.sha256 witnessScript = program ∧ Accepts L msg prog st)

/-- Under the explicit bridge, both signatures make the funding output
spendable for the existing `FundingSpendableBy2of2` predicate. -/
theorem fundingSpendableBy2of2_of_both_sign
    (verify : Bitcoin.Data.Script → Bitcoin.Data.WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray)
    (p : FundingParams) (vtx : Bitcoin.Data.Tx) (dummy s1 s2 : ByteArray)
    (hbridge : ConsensusSpendBridge verify L msg)
    (hlink : p.witnessScriptHash = L.sha256 p.witnessScript.bytes)
    (h1 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1.bytes msg s1 = true)
    (h2 : L.sigCheck
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2.bytes msg s2 = true) :
    FundingSpendableBy2of2 verify p vtx
      ([dummy, s1, s2] ++ [p.witnessScript.bytes]) := by
  unfold FundingSpendableBy2of2
  have hspend := fundingParams_spendable L msg p dummy s1 s2 hlink h1 h2
  have hscript : p.fundingScriptPubKey = p2wsh p.witnessScriptHash := rfl
  rw [hscript, hlink]
  have h := (hbridge vtx (L.sha256 p.witnessScript.bytes) p.witnessScript.bytes
    (fundingProg (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1
      (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2)
    [s2, s1, dummy] hspend.1).mpr ⟨rfl, hspend.2.2⟩
  simpa [fundingWitness_reverse] using h

/-- Under the explicit bridge, the revocation branch spends `to_local`
without any CSV condition. -/
theorem toLocalSpendable_revocation_of_bridge
    (verify : Bitcoin.Data.Script → Bitcoin.Data.WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (vtx : Bitcoin.Data.Tx)
    (hbridge : ConsensusSpendBridge verify L msg)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    verify
      (p2wsh (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, oneByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes])
      vtx = true := by
  have h' := (hbridge vtx
    (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
    (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
    (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]
    (toLocalProg_serialize revocationKey delayedPaymentKey csv)).mpr
    ⟨rfl, exec_toLocal_revocation L msg revocationKey delayedPaymentKey csv sig h⟩
  simpa using h' 

/-- Under the explicit bridge, the delayed branch spends `to_local` when the
CSV law holds. -/
theorem toLocalSpendable_delayed_of_bridge
    (verify : Bitcoin.Data.Script → Bitcoin.Data.WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (vtx : Bitcoin.Data.Tx)
    (hbridge : ConsensusSpendBridge verify L msg)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    verify
      (p2wsh (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, zeroByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes])
      vtx = true := by
  have h' := (hbridge vtx
    (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
    (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
    (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]
    (toLocalProg_serialize revocationKey delayedPaymentKey csv)).mpr
    ⟨rfl, exec_toLocal_delayed L msg revocationKey delayedPaymentKey csv sig hcsv h⟩
  simpa using h' 

/-! ## Limits (what is *not* proved) -/

/-- The model's truthiness diverges from Core's `cast_to_bool` on a
non-minimal false encoding: `#[0x00]` is "true" here and false in Bitcoin.
This is why no theorem in this module may be read as consensus validation. -/
theorem truthy_nonminimal_true : truthy (ByteArray.mk #[0x00]) = true := rfl

/-- `OP_CHECKMULTISIG` here is the 2-of-2 instantiation only; a script whose
first count push is not `OP_2` errors. -/
theorem exec_wrong_multisig_count (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray) :
    execStmts L msg
      [ .basic (.num 3), .basic (.push a.bytes), .basic (.push b.bytes),
        .basic (.num 2), .basic .checkMultiSig ] [s2, s1, dummy] = none := by
  simp [execStmts, execStmt, step]

/-- A wrong revealed witness script is not the P2WSH spend: the serializer
equation identifies the executed program's script bytes. -/
theorem not_p2wshSpend_of_script_ne (L : InterpreterLaws) (msg : ByteArray)
    (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack)
    (hne : serializeStmts prog ≠ witnessScript) :
    ¬ P2WSHSpend L msg program witnessScript prog st := by
  intro h
  exact hne h.1

/-- A hash mismatch is rejected before execution: no `P2WSHSpend` exists. -/
theorem not_p2wshSpend_of_hash_ne (L : InterpreterLaws) (msg : ByteArray)
    (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack)
    (hne : L.sha256 witnessScript ≠ program) :
    ¬ P2WSHSpend L msg program witnessScript prog st := by
  intro h
  exact hne h.2.1

end LnLean.Proofs.Bitcoin.SpendTargets
