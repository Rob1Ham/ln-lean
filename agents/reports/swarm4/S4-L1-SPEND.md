# S4-L1-SPEND — execution-level spend bridge for the funding and `to_local` outputs

**Lane:** `S4-L1-SPEND` (issue `L1-01`, `L1-02`)
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Branch / base:** `repair/integrated` @ `47189fe` (proof-wave 3 closed, catalog 48/48)
**Status:** completed; sorry-free, no new axioms, additive seam changes only.
The result is an **explicit conditional script-execution bridge**, not a
consensus-spendability theorem. This is stated precisely below.

## 1. Result in one paragraph

The tree previously had byte templates and structural commitments for the
BOLT 3 P2WSH funding output and the two-branch `to_local` output, but no
execution semantics at all. This lane adds a small, explicit stack machine
(`InterpreterLaws`, `Instr`/`Stmt`, `step`, `execStmts`, `Accepts`) whose
serializer is *proved* equal to the seam's byte templates, and proves:

* a 2-of-2 funding output is spendable whenever both ordered funding keys
  sign, the revealed witness script is the 2-of-2 script, and its SHA-256 is
  the committed P2WSH program;
* `to_local` is spendable through the **revocation branch** with no CSV
  condition, and through the **delayed branch** when the CSV law holds and
  the delayed key signs;
* one signature, a wrong key, a bad CSV condition, an empty witness, and a
  wrong revealed script are all rejected (mechanized negatives).

The semantics' missing consensus pieces are named fields of
`InterpreterLaws` (`sigCheck`, `csvOk`, `cltvOk`, `sha256`, `hash160`), and
the only link to a real L1 verifier is the explicit, unproved
`ConsensusSpendBridge` hypothesis. No theorem claims Bitcoin consensus
acceptance.

**Important discovery.** The vendored tree *does* contain a real interpreter:
`vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean` has `evalScriptBytes`
(`:1130`), `executeWitnessScript` (`:1167`), `verifyWitnessProgram` with the
P2WSH branch (`:1211`), `checkMultiSig` (`:1038`) and `verifyScriptFull`
(`:1305`), plus the hash floor `Bitcoin.Interpreter.Hashes.hashSha256`
(`Hashes.lean:125`). It is **not** imported by `LnLean`, and only four vendor
modules (`Data/Basic`, `Data/Script`, `Data/Tx`, `RuleAttr`) are built in this
worktree, so connecting it is a separate, larger step (see §10). This lane did
not import it, and §10 gives the exact integration path.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Bitcoin/Seam.lean` | **Additive only**: `toLocalDelayBytes`, `toLocalDelayPush_eq_pushData_delayBytes`, `toLocalDelayBytes_size`. No existing signature, body, or theorem changed. |
| `LnLean/Proofs/Bitcoin/SpendTargets.lean` | New module, 744 lines, 32 theorems. |
| `agents/reports/swarm4/S4-L1-SPEND.md` | This report. |

`git diff` on `Seam.lean` shows only insertions after the existing flat
`toLocalScript` definition; `toLocalDelayPush` and every earlier declaration
are byte-for-byte unchanged.

## 3. The model (all in `LnLean.Proofs.Bitcoin.SpendTargets`)

```lean
abbrev Stack := List ByteArray          -- head = top of stack
def oneByte : ByteArray                 -- #[0x01]
def zeroByte : ByteArray                -- empty
def truthy (d : ByteArray) : Bool       -- d.size != 0  (see §8)
def boolBytes (b : Bool) : ByteArray

structure InterpreterLaws where
  sigCheck : ByteArray → ByteArray → ByteArray → Bool   -- pk, sighash msg, sig
  csvOk    : ByteArray → Bool                            -- raw delay element
  cltvOk   : ByteArray → Bool
  sha256   : ByteArray → ByteArray
  hash160  : ByteArray → ByteArray

inductive Instr
  | push (d : ByteArray) | num (n : Nat) | dup | drop
  | hash160 | sha256 | equal | equalVerify | checkSig | checkMultiSig
  | csv | cltv

inductive Stmt
  | basic (i : Instr)
  | ite (t e : List Stmt)               -- one level; no nested IF

def Instr.serialize : Instr → ByteArray
def Stmt.serialize  : Stmt  → ByteArray
def serializeStmts  : List Stmt → ByteArray

def step (L) (msg) : Instr → Stack → Option Stack
def execStmt  (L) (msg) : Stmt → Stack → Option Stack
def execStmts (L) (msg) : List Stmt → Stack → Option Stack

def Accepts (L) (msg) (prog) (st) : Prop :=
  execStmts L msg prog st = some [oneByte]

def P2WSHSpend (L) (msg) (program witnessScript : ByteArray)
    (prog : List Stmt) (st : Stack) : Prop :=
  serializeStmts prog = witnessScript ∧
    L.sha256 witnessScript = program ∧
    Accepts L msg prog st

def SpendableOutput (L) (msg) (spk : Bitcoin.Data.Script)
    (witness : Bitcoin.Data.WitnessStack) : Prop :=
  ∃ program witnessScript prog st,
    spk = p2wsh program ∧ witness = st.reverse ++ [witnessScript] ∧
      P2WSHSpend L msg program witnessScript prog st

def fundingProg (a b : PubKey) : List Stmt :=
  [.basic (.num 2), .basic (.push a.bytes), .basic (.push b.bytes),
   .basic (.num 2), .basic .checkMultiSig]

def toLocalProg (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) : List Stmt :=
  [.ite [.basic (.push revocationKey.bytes)]
        [.basic (.push (delayBytes csv)), .basic .csv, .basic .drop,
         .basic (.push delayedPaymentKey.bytes)],
   .basic .checkSig]

def delayBytes (csv : Blocks) : ByteArray := toLocalDelayBytes csv
```

`OP_CHECKMULTISIG` is modelled as its 2-of-2 instantiation (the only shape
BOLT 3 uses for funding): it pops the count pushes and checks
`sigCheck pkA msg sA && sigCheck pkB msg sB`, ignoring the dummy's value.
`OP_CSV`/`OP_CLTV` inspect the top element and leave it on the stack (BIP
112/65), then `OP_DROP` removes it. `OP_IF` selects the branch on
`truthy`; `OP_ENDIF` is structural.

## 4. Exact signatures

All names are fully qualified under `LnLean.Proofs.Bitcoin.SpendTargets`.
Machine stacks are head = top; the BOLT witness order is the reverse, which
`SpendableOutput` and `fundingWitness_reverse` state explicitly.

### 4.1 Byte-level agreement with the seam (no hypotheses)

```lean
theorem fundingProg_serialize (a b : PubKey) :
    serializeStmts (fundingProg a b) = TwoOfTwoScriptBytes a b

theorem fundingProg_serialize_params (p : FundingParams) :
    serializeStmts
        (fundingProg (orderedFundingKeys p.localFundingKey p.remoteFundingKey).1
          (orderedFundingKeys p.localFundingKey p.remoteFundingKey).2) =
      p.witnessScript.bytes

theorem toLocalProg_serialize (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes

theorem toLocalProg_serialize_template (revocationKey delayedPaymentKey : PubKey)
    (csv : Blocks) :
    serializeStmts (toLocalProg revocationKey delayedPaymentKey csv) =
      (toLocalWitnessScript revocationKey delayedPaymentKey csv).bytes
```

`fundingProg_serialize` uses
`FundingScriptTargets.TwoOfTwoScriptBytes`; `fundingProg_serialize_params`
uses `FundingScriptTargets.witnessScript_eq_TwoOfTwoScriptBytes` (either key
order). `toLocalProg_serialize_template` uses
`ToLocalScriptTargets.toLocalScriptFull_eq_template`.

### 4.2 Funding execution and spend

```lean
theorem exec_funding (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [oneByte]

theorem fundingOutput_spendable (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    P2WSHSpend L msg (L.sha256 (TwoOfTwoScriptBytes a b))
      (TwoOfTwoScriptBytes a b) (fundingProg a b) [s2, s1, dummy]

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
      [s2, s1, dummy]

theorem fundingOutput_spendable_output (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = true) :
    SpendableOutput L msg (p2wsh (L.sha256 (TwoOfTwoScriptBytes a b)))
      ([dummy, s1, s2] ++ [TwoOfTwoScriptBytes a b])

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
          ([dummy, s1, s2] ++ [p.witnessScript.bytes])

theorem fundingWitness_reverse (dummy s1 s2 : ByteArray) :
    ([s2, s1, dummy] : Stack).reverse = [dummy, s1, s2]
```

`fundingConfirmed_spendable_output` is the composition with the existing
`FundingConfirmed` predicate: the spend applies to the actual indexed
`TxOut`, not only to a reconstructed script.

### 4.3 `to_local` execution and spend

```lean
theorem exec_toLocal_revocation (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [oneByte]

theorem exec_toLocal_revocation_independent_of_csv (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray) (_hcsv : L.csvOk (delayBytes csv) = false)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [oneByte]

theorem exec_toLocal_delayed (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [zeroByte, sig] = some [oneByte]

theorem toLocalOutput_revocation_spendable (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    P2WSHSpend L msg
      (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]

theorem toLocalOutput_delayed_spendable (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    P2WSHSpend L msg
      (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes)
      (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes
      (toLocalProg revocationKey delayedPaymentKey csv) [zeroByte, sig]

theorem toLocalOutput_revocation_spendable_output (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = true) :
    SpendableOutput L msg
      (toLocalScriptPubKey
        (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, oneByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes])

theorem toLocalOutput_delayed_spendable_output (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = true)
    (h : L.sigCheck delayedPaymentKey.bytes msg sig = true) :
    SpendableOutput L msg
      (toLocalScriptPubKey
        (L.sha256 (toLocalScriptFull revocationKey delayedPaymentKey csv).bytes))
      ([sig, zeroByte] ++ [(toLocalScriptFull revocationKey delayedPaymentKey csv).bytes])

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
            [(toLocalScriptFull p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes])
```

The witness for the revocation branch is `[sig, 0x01, witnessScript]`; for
the delayed branch it is `[sig, empty, witnessScript]` (Bitcoin order,
revealed script last). `commitmentOutputs_toLocal_delayed_spendable` locates
the `to_local` entry in the existing zero-HTLC `commitmentOutputs` list and
spends its actual `scriptPubKey`.

### 4.4 The L1-verifier bridge (explicit hypothesis)

```lean
def ConsensusSpendBridge
    (verify : Bitcoin.Data.Script → Bitcoin.Data.WitnessStack → Bitcoin.Data.Tx → Bool)
    (L : InterpreterLaws) (msg : ByteArray) : Prop :=
  ∀ (vtx : Bitcoin.Data.Tx) (program witnessScript : ByteArray)
      (prog : List Stmt) (st : Stack),
    serializeStmts prog = witnessScript →
    (verify (p2wsh program) (st.reverse ++ [witnessScript]) vtx = true ↔
      L.sha256 witnessScript = program ∧ Accepts L msg prog st)

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
      ([dummy, s1, s2] ++ [p.witnessScript.bytes])

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
      vtx = true

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
      vtx = true
```

`FundingSpendableBy2of2` is the existing predicate in
`LnLean/Bitcoin/Funding.lean`, so `fundingSpendableBy2of2_of_both_sign` is a
direct strengthening of the old bridge: the only remaining hypothesis is the
verifier agreement itself (plus the hash link and the signature laws).

### 4.5 Negative / limits theorems

```lean
theorem exec_funding_one_signature (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = false) :
    execStmts L msg (fundingProg a b) [s2, s1, dummy] = some [zeroByte]

theorem not_accepts_funding_one_signature (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray)
    (h1 : L.sigCheck a.bytes msg s1 = true)
    (h2 : L.sigCheck b.bytes msg s2 = false) :
    ¬ Accepts L msg (fundingProg a b) [s2, s1, dummy]

theorem exec_toLocal_delayed_csv_fails (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (hcsv : L.csvOk (delayBytes csv) = false) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [zeroByte, sig] = none

theorem exec_toLocal_empty_witness (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv) [] = none

theorem exec_toLocal_revocation_bad_sig (L : InterpreterLaws) (msg : ByteArray)
    (revocationKey delayedPaymentKey : PubKey) (csv : Blocks) (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = false) :
    execStmts L msg (toLocalProg revocationKey delayedPaymentKey csv)
      [oneByte, sig] = some [zeroByte]

theorem not_accepts_toLocal_revocation_bad_sig (L : InterpreterLaws)
    (msg : ByteArray) (revocationKey delayedPaymentKey : PubKey) (csv : Blocks)
    (sig : ByteArray)
    (h : L.sigCheck revocationKey.bytes msg sig = false) :
    ¬ Accepts L msg (toLocalProg revocationKey delayedPaymentKey csv) [oneByte, sig]

theorem truthy_nonminimal_true : truthy (ByteArray.mk #[0x00]) = true

theorem exec_wrong_multisig_count (L : InterpreterLaws) (msg : ByteArray)
    (a b : PubKey) (dummy s1 s2 : ByteArray) :
    execStmts L msg
      [.basic (.num 3), .basic (.push a.bytes), .basic (.push b.bytes),
       .basic (.num 2), .basic .checkMultiSig] [s2, s1, dummy] = none

theorem not_p2wshSpend_of_script_ne (L : InterpreterLaws) (msg : ByteArray)
    (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack)
    (hne : serializeStmts prog ≠ witnessScript) :
    ¬ P2WSHSpend L msg program witnessScript prog st

theorem not_p2wshSpend_of_hash_ne (L : InterpreterLaws) (msg : ByteArray)
    (program witnessScript : ByteArray) (prog : List Stmt) (st : Stack)
    (hne : L.sha256 witnessScript ≠ program) :
    ¬ P2WSHSpend L msg program witnessScript prog st
```

## 5. Build results

Exact commands (shared lock, one thread):

```sh
cd /home/ubuntu/ln-lean-repair
export PATH=/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Bitcoin.SpendTargets
# ✔ [22/22] Built LnLean.Proofs.Bitcoin.SpendTargets (1.8s)
# Build completed successfully (22 jobs).  RC 0

LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Bitcoin.Seam
# Build completed successfully (8 jobs).  RC 0
```

No warnings on a fresh compile (`grep -i 'warning\|error'` on the build log:
no matches). No full `lake build`, no `collect-obligations.py`, no
`collect-anchors.py`, no Git write command was run.

No downstream `LnLean` module imports `SpendTargets` yet, so there is no
other direct module to build; `LnLean.lean` is forbidden for this lane (see
§9 for the one-line integration).

## 6. Axiom audit

`#print axioms` on all 32 theorems in
`LnLean/Proofs/Bitcoin/SpendTargets.lean` and the three new Seam
declarations. Every result is a subset of
`{propext, Quot.sound, Classical.choice}`.

| Declaration group | Axioms |
|---|---|
| `fundingProg_serialize`, `fundingProg_serialize_params`, `toLocalProg_serialize`, `toLocalProg_serialize_template` | `propext`, `Quot.sound` |
| `fundingWitness_reverse`, `truthy_nonminimal_true` | none |
| `zeroByte_ne_oneByte` | `propext`, `Quot.sound` |
| `exec_funding`, `exec_funding_one_signature`, `not_accepts_funding_one_signature` | `propext`, `Classical.choice`, `Quot.sound` |
| `fundingOutput_spendable`, `fundingParams_spendable`, `fundingOutput_spendable_output`, `fundingConfirmed_spendable_output` | `propext`, `Classical.choice`, `Quot.sound` |
| `exec_toLocal_revocation`, `exec_toLocal_revocation_independent_of_csv`, `exec_toLocal_delayed` | `propext`, `Classical.choice`, `Quot.sound` |
| `exec_toLocal_delayed_csv_fails`, `exec_toLocal_empty_witness`, `exec_toLocal_revocation_bad_sig`, `not_accepts_toLocal_revocation_bad_sig` | `propext`, `Classical.choice`, `Quot.sound` |
| `toLocalOutput_revocation_spendable`, `toLocalOutput_delayed_spendable`, `toLocalOutput_revocation_spendable_output`, `toLocalOutput_delayed_spendable_output`, `commitmentOutputs_toLocal_delayed_spendable` | `propext`, `Classical.choice`, `Quot.sound` |
| `fundingSpendableBy2of2_of_both_sign`, `toLocalSpendable_revocation_of_bridge`, `toLocalSpendable_delayed_of_bridge` | `propext`, `Classical.choice`, `Quot.sound` |
| `exec_wrong_multisig_count`, `not_p2wshSpend_of_script_ne`, `not_p2wshSpend_of_hash_ne` | `propext`, `Classical.choice`, `Quot.sound` |
| `LnLean.Bitcoin.toLocalDelayBytes`, `toLocalDelayPush_eq_pushData_delayBytes` | none |
| `LnLean.Bitcoin.toLocalDelayBytes_size` | `propext` |

No module-specific axiom, no `sorryAx`, no `Classical.choice` beyond the
standard `omega`/`by_cases` usage.

## 7. Forbidden-construct scan

```sh
grep -nE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b' \
  LnLean/Bitcoin/Seam.lean LnLean/Proofs/Bitcoin/SpendTargets.lean
# NO FORBIDDEN CONSTRUCTS
```

(The scan was clean after rewording one doc-comment sentence that contained
the word "axiom"; the source now has no occurrence of the token at all.)

## 8. Scope caveats — what is *not* proved

This is an execution model, **not** Bitcoin consensus. Precisely:

1. **No consensus connection.** `ConsensusSpendBridge` is an unproved `Prop`.
   The only way to obtain a statement about a real verifier is to prove that
   hypothesis (or instantiate it with a proved interpreter). The vendored
   `Bitcoin.Interpreter.verifyScript` is not imported.
2. **No sighash.** `sigCheck` takes the 32-byte message as a parameter; BIP
   143 preimage construction, `SIGHASH_ALL` handling, and `Bitcoin.SigHash`
   are not used. Assumption C3 is only visible as the `sigCheck` field.
3. **Truthiness diverges from Core.** `truthy d := d.size != 0`, so
   `#[0x00]` is true here (mechanized as `truthy_nonminimal_true`) while
   Core's `cast_to_bool` says false; `#[0x80]` (negative zero) is also true
   here. The model is exact only for the canonical `0x01` / empty selectors.
4. **`OP_CHECKMULTISIG` is 2-of-2 only.** `n`/`m` must encode `OP_2`; the
   dummy is ignored (NULLDUMMY is not enforced); key/signature ordering is
   the fixed BOLT 3 order; there is no "skip a key" multisig algorithm.
5. **Signature errors push `false`.** A malformed DER signature (DERSIG) or
   `NULLFAIL` would be a script error in Core; here it is a failed `sigCheck`
   and therefore `false`. `checkSig` also never errors on a bad encoding.
6. **CSV/CLTV are abstract.** `csvOk`/`cltvOk` take the raw element and are
   supplied by the caller. `delayBytes` is the scaffold's fixed two-byte
   little-endian encoding, not minimal `CScriptNum`; it is exact for the
   BOLT 2 `u16` `to_self_delay` field, but not for all `CScriptNum` values.
   `cltvOk` is present in `InterpreterLaws` but unused by the two templates
   (neither contains `OP_CLTV`).
7. **No byte decoder.** The script-bytes link is the *serializer* direction:
   `serializeStmts prog = script.bytes`. A decoder theorem
   (`Bitcoin.Script.Parser.parseWire` of the serialized bytes yields `prog`)
   is not proved. The legacy `Bitcoin.Data.Script.parse` cannot parse these
   scripts at all (no `OP_CHECKMULTISIG`/`OP_IF` constructors; see
   `FundingScriptTargets` and `FundingProps.witnessScript_parse_eq_none_of_wellFormed`).
8. **No nested `OP_IF`.** `Stmt.ite` is one level. The funding and
   `to_local` templates need only one level; the offered/received HTLC
   witness scripts (`ScriptTemplates.offeredHtlcWitnessScript`,
   `receivedHtlcWitnessScript`) have nested conditionals and are out of
   scope.
9. **No chain-level facts.** `FundingConfirmed` remains a predicate; no
   confirmation, reorg, fee, weight, or mempool rule is proved here.
10. **Key validity is length-only.** `PubKey.Valid` checks 33 bytes; no
    secp256k1 point parsing or validity is proved.
11. **Fixed output value not checked.** Spendability does not depend on the
    output value; `FundingConfirmed` already fixes it, but this module does
    not add a value theorem.

## 9. Recommended catalog / documentation integration

The integrator owns `LnLean.lean`, `Obligations.lean`, `Traceability.lean`,
`PhaseC3/AxiomAudit.lean`, and `docs/`. Suggested exact steps:

1. **Root import** (required before any full-tree gate):
   ```lean
   import LnLean.Proofs.Bitcoin.SpendTargets
   ```
   in `LnLean.lean` (alphabetically near the other `LnLean.Proofs.Bitcoin.*`
   imports).
2. **Axiom audit**: add the headline theorems to
   `LnLean/Proofs/PhaseC3/AxiomAudit.lean`, at minimum
   `fundingOutput_spendable_output`,
   `fundingConfirmed_spendable_output`,
   `toLocalOutput_revocation_spendable_output`,
   `toLocalOutput_delayed_spendable_output`,
   `commitmentOutputs_toLocal_delayed_spendable`, and
   `not_accepts_funding_one_signature`.
3. **Catalog**: do **not** silently replace the existing `LN-L1-001` /
   `LN-L1-004` targets with these theorems, because the new results are
   conditional on `InterpreterLaws` and (for the verifier form) on
   `ConsensusSpendBridge`. Recommended:
   * keep `LN-L1-001`/`LN-L1-004` as the structural/hash-commitment rows;
   * add a new row, e.g. `LN-L1-007 — Conditional P2WSH/OP_CHECKMULTISIG
     execution bridge`, `leanTarget :=
     "LnLean.Proofs.Bitcoin.SpendTargets.fundingConfirmed_spendable_output"`,
     `status := .proved`, with the scope note:
     > Conditional on explicit `InterpreterLaws` (`sigCheck`, `sha256`), the
     > construction invariant `witnessScriptHash = sha256(witnessScript)`, and
     > a local stack-machine semantics; not Bitcoin consensus. The
     > L1-verifier form is `fundingSpendableBy2of2_of_both_sign`, conditional
     > on the unproved `ConsensusSpendBridge`.
   * add `LN-L1-008 — Conditional to_local revocation/delayed execution
     bridge`, `leanTarget :=
     "LnLean.Proofs.Bitcoin.SpendTargets.commitmentOutputs_toLocal_delayed_spendable"`,
     `status := .proved`, with the note that the revocation branch is
     `toLocalOutput_revocation_spendable_output` (no CSV hypothesis) and the
     delayed branch needs `csvOk (delayBytes toSelfDelay) = true`.
   * if a single-row target is preferred, use
     `fundingOutput_spendable_output` and
     `toLocalOutput_delayed_spendable_output` (they avoid
     `FundingConfirmed`/`CommitmentParams` plumbing and still carry every
     assumption).
4. **`docs/OPEN-ISSUES.md`**: keep `L1-01`/`L1-02` **open** (the consensus
   bridge is still unproved), but update their evidence column to point at
   this report and state the new boundary:
   * `L1-01`: "execution-level conditional bridge proved
     (`fundingConfirmed_spendable_output`); consensus bridge via the
     vendored `Bitcoin.Interpreter.verifyScript` still open."
   * `L1-02`: "both `to_local` branches execute under explicit CSV/signature
     laws (`toLocalOutput_*_spendable_output`); consensus bridge open."
   * `MODEL-01`: revise "no script interpreter" to "the vendored
     `Bitcoin.Interpreter` exists but is not connected to the LnLean
     scripts; this lane supplies a local model and the exact bridge
     predicate."
5. **`docs/ASSUMPTIONS.md`**: the new `InterpreterLaws` fields should be
   listed under the L1 semantics section as *modelled interfaces*: `sigCheck`
   = C3 at the point of use, `csvOk`/`cltvOk` = BIP 112/65 laws, `sha256` =
   C1, `hash160` = C2. No new cryptographic assumption is introduced.
6. **`docs/THEOREM-INDEX.md`** (if generated from the catalog): regenerate
   only after the new rows are added; do not cite the module as
   "consensus spendability".

## 10. Exact blockers and next steps

1. **Vendored interpreter import is the main blocker.** `Bitcoin.Interpreter`
   is a real interpreter, but importing `Bitcoin.Interpreter.Interface`
   pulls `Script.Parser`, `Activation`, `Crypto.Seam`, `Numeric`, `Hashes`,
   and a large transitive chain (only `Data/Basic`, `Data/Script`, `Data/Tx`,
   `RuleAttr` are currently built in `vendor/btc-lean-core/.lake`). The next
   lane should:
   * build `Bitcoin.Interpreter.Interface` in the vendor package (measure
     time/space under the lock);
   * prove the P2WSH dispatch lemma for `verifyScriptFull`/`verifyWitnessProgram`
     (`Defs.lean:1211-1240`), i.e. if `witness.getLast! = witnessScript`,
     `hashSha256 witnessScript = program`, and
     `evalScriptBytes … witnessScript (witness.dropLast).reverse … = .ok [true]`,
     then `verifyScriptFull … = .ok`;
   * prove the 2-of-2 `checkMultiSig` case (`Defs.lean:1038-1090`);
   * prove `OP_CSV`/`OP_IF`/`OP_DROP`/`OP_CHECKSIG` steps for the
     `to_local` script against `checkSequenceDef` and the `ScriptChecker`.
2. **Sighash / checker instantiation.** `verifyScript` takes a
   `ScriptChecker` (crypto seam + `LocktimeEnv`); the adapter from a `Tx`
   and a BIP 143 sighash to that checker is not written. `Bitcoin.SigHash`
   exists in the vendor tree but is not imported by LnLean.
3. **Hash floor.** `Bitcoin.Interpreter.Hashes.hashSha256` is a concrete
   implementation; the bridge must identify it with `InterpreterLaws.sha256`
   (or instantiate `L.sha256 := Bitcoin.Interpreter.hashSha256`).
4. **Truthiness / NULLDUMMY / DERSIG.** Replacing `truthy` with
   `Bitcoin.Interpreter.castToBool` and enforcing the dummy and encoding
   rules are small but necessary for a consensus-level claim.
5. **Decoder.** Proving `parseWire (serializeStmts prog) = some …` would
   remove the serializer-only asymmetry and make the byte link two-way.
6. **Key/curve validity.** A real secp256k1 encoding/validity model is
   needed before any claim about actual funding keys.
7. **Nested conditionals** are required for the HTLC witness scripts; the
   `Stmt` AST and branch rule must be extended (or a different interpreter
   used) before `LN-L1-005`-style HTLC execution can be attempted.

## 11. Shared files not edited

For the avoidance of doubt, this lane did **not** modify:

* `LnLean.lean`, `LnLean/Proofs/Obligations.lean`,
  `LnLean/Proofs/Traceability.lean`, `LnLean/Proofs/PhaseC3/AxiomAudit.lean`
* `docs/**`, `scripts/**`, `agents/status/**`
* `vendor/btc-lean-core/**`
* any other lane's files (`Channel/HTLC.lean`, `Protocol/Messages.lean`,
  `Routing/Gossip.lean`, `Proofs/Channel/*`, `Proofs/Protocol*`,
  `Proofs/Routing/*`, `.github/**`, `tests/**`, `README.md`)

No `git add`, `commit`, `push`, `checkout`, `reset`, `stash`, or file
deletion was performed. The only pre-existing working-tree changes touched by
this lane are the additive `Seam.lean` insertions listed in §2.
