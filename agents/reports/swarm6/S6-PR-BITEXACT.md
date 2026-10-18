# S6-PR-BITEXACT — Exact BOLT 3 commitment/HTLC byte layout and refinement

**Lane:** `S6-PR-BITEXACT` (`PR-05`, `PR-02`).
**Worktree:** `/home/ubuntu/ln-lean-repair`
**Verdict:** implemented in the owned module and fully built/verified in a
repaired tree copy. The real shared tree is currently blocked by a concurrent
lane's break in `LnLean/Proofs/Conservation.lean` (not owned by this lane); see
§8. The owned file is additive: one import plus a new section, with no existing
declaration changed.

- Owned files touched:
  - `LnLean/Proofs/Channel/SighashTargets.lean` — additive extension,
    +490 lines, new §12 at line 961.
  - `agents/reports/swarm6/S6-PR-BITEXACT.md` — this report.
- Not modified: `Messages.lean`, `Commitment.lean`, `LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`,
  `scripts/check-final.py`, shared docs, other lanes' files, vendor sources.
- No Git write was performed.
- No `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` /
  `@[implemented_by]` was introduced (scan in §6).

## 1. Result in one paragraph

The module now contains an explicit BOLT 3-shaped commitment transaction
(`CommitmentWire`) whose bytes are produced by the **vendored transaction
serializer** (`Bitcoin.Data.serTx`), an explicit 10-field BIP 143 preimage
(`Bip143Preimage`) in consensus order, and an explicit HTLC second-stage
transaction (`HtlcWire`). The commitment and HTLC layouts are proved to be
accepted and recovered exactly by the vendored parser
(`decTxCore ∘ bL = .ok (tx, [])`), with exact size formulas and concrete
`decide`-checked vectors: a 125-byte commitment transaction matching BOLT 3
Appendix A's base size, and a 158-byte BIP 143 preimage for a one-byte
`scriptCode`. A bridge (`CommitmentMeta`, `viewOfWire`, `Obscures`, `SharedEq`)
then proves that the pre-existing structural serializer `commitmentPreimage`
is a function of exactly the wire fields it models — funding outpoint, output
values, and the obscured commitment number — and a mechanised counterexample
proves the abstraction is **strict**: the structural view drops output
`scriptPubKey`s, so equal structural views do not imply equal wire bytes.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Proofs/Channel/SighashTargets.lean` | Added `import Bitcoin.Serialization.Interface` (line 86) and §12 (line 961): exact tx/preimage/HTLC layouts, parser round-trips, size theorems, concrete vectors, and the structural-refinement bridge with positive and negative results. |
| `agents/reports/swarm6/S6-PR-BITEXACT.md` | This report. |

The diff is exactly 490 insertions and 0 deletions in the owned module. Every
pre-existing declaration, including `SighashProduces` (line 454), `honestFull`
(line 419), `honest_commitment_signed_full_covers` (line 733), and the three
legacy negatives (lines 796/804/814), is untouched and still builds.

## 3. Exact layout definitions and theorems

All new declarations live in
`namespace LnLean.Proofs.Channel.SighashTargets` and open
`Bitcoin.Data` / `Bitcoin.Serialization` only for §12, so the existing
namespace/opening discipline is unchanged.

### 3.1 Integer and CompactSize primitives

```lean
def exactU32 (x : UInt32) : ByteArray := Bitcoin.Data.serU32 x
def exactU64 (x : UInt64) : ByteArray := Bitcoin.Data.serU64 x
def exactCS  (n : Nat)    : ByteArray := Bitcoin.Data.compactSizeEnc n

theorem exactU32_size (x : UInt32) : (exactU32 x).size = 4
theorem exactU64_size (x : UInt64) : (exactU64 x).size = 8
theorem exactCS_size_zero : (exactCS 0).size = 1

def compactSizeWidth (n : Nat) : Nat :=
  if n < 0xfd then 1 else if n ≤ 0xffff then 3
  else if n ≤ 0xffffffff then 5 else 9

theorem compactSizeEnc_size (n : Nat) :
    (Bitcoin.Data.compactSizeEnc n).size = compactSizeWidth n

theorem foldl_append_size {α : Type} (l : List α) (f : α → ByteArray)
    (init : ByteArray) :
    (l.foldl (fun acc x => acc ++ f x) init).size =
      init.size + (l.map (fun x => (f x).size)).sum
```

`exactU32`/`exactU64`/`exactCS` are transparent aliases for the vendored
serializers, so every width lemma is about the actual bytes used below.

### 3.2 Commitment transaction layout

```lean
structure ExactCommitmentOutput where
  output : CommitmentOutput
  scriptPubKey : ByteArray

def ExactCommitmentOutput.toTxOut (o : ExactCommitmentOutput) : TxOut

structure CommitmentWire where
  version : UInt32
  fundingTxid : ByteArray
  fundingOutputIndex : UInt32
  sequence : UInt32
  outputs : List ExactCommitmentOutput
  locktime : UInt32

def CommitmentWire.toTx (w : CommitmentWire) : Tx
def CommitmentWire.txBytes (w : CommitmentWire) : ByteArray :=
  Bitcoin.Data.serTx w.toTx

def CommitmentWire.WellFormed (w : CommitmentWire) : Prop :=
  w.fundingTxid.size = 32 ∧
  w.outputs.length ≤ Bitcoin.Serialization.MAX_SIZE ∧
  (∀ o ∈ w.outputs, o.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE ∧
     o.output.value < 9223372036854775808)

theorem CommitmentWire.wireDomain_toTx (w : CommitmentWire) (h : w.WellFormed) :
    Bitcoin.Serialization.wireDomain w.toTx

theorem CommitmentWire.txBytes_parse (w : CommitmentWire) (h : w.WellFormed) :
    Bitcoin.Serialization.decTxCore (Bitcoin.Serialization.bL w.txBytes) =
      .ok (w.toTx, [])

theorem CommitmentWire.txBytes_size (w : CommitmentWire) :
    w.txBytes.size =
      4 + 1 + w.fundingTxid.size + 4 + 1 + 4 +
        compactSizeWidth w.outputs.length +
        (w.outputs.map (fun o => 8 + compactSizeWidth o.scriptPubKey.size +
          o.scriptPubKey.size)).sum + 4
```

`toTx` fixes version, one funding input (`scriptSig = empty`, supplied
sequence), the supplied output list in order, the supplied locktime, and an
empty witness list. The proof of `txBytes_parse` goes through
`bL txBytes = encTxL toTx` and the vendored round-trip theorem
`decTxCore_encTxL`; it is therefore a genuine parser round-trip, not a
re-encoding claim.

### 3.3 Concrete 125-byte commitment vector

```lean
def vectorFundingTxid : ByteArray := hash32 0x11
def vectorOutput1 : ExactCommitmentOutput   -- .toRemote 1000, P2WPKH 0x00 0x14 + 20×0x22
def vectorOutput2 : ExactCommitmentOutput   -- .toLocal 2000,  P2WSH  0x00 0x20 + 32×0x33
def vectorWire : CommitmentWire             -- version 2, index 0, sequence 0x80000000,
                                            -- locktime 0x20000000

theorem vectorCommitmentTx :
    Bitcoin.Serialization.bL vectorWire.txBytes =
      [0x02, 0x00, 0x00, 0x00, 0x01] ++ List.replicate 32 0x11 ++
      [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x02,
       0xe8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16, 0x00, 0x14] ++
      List.replicate 20 0x22 ++
      [0xd0, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22, 0x00, 0x20] ++
      List.replicate 32 0x33 ++
      [0x00, 0x00, 0x00, 0x20]

theorem vectorCommitmentTx_size :
    (Bitcoin.Serialization.bL vectorWire.txBytes).length = 125
```

Both are closed by `decide` (with `maxRecDepth 10000`). The byte list is the
BOLT 3 base commitment transaction shape: version, one input, 0xffffffff
funding index, obscured-sequence high bit, two outputs, obscured-locktime high
bit. The size 125 agrees with BOLT 3 Appendix A's base commitment size for two
non-HTLC outputs.

### 3.4 BIP 143 preimage layout

```lean
structure Bip143Preimage where
  version : UInt32
  hashPrevouts : ByteArray
  hashSequence : ByteArray
  outpointTxid : ByteArray
  outpointIndex : UInt32
  scriptCode : ByteArray
  amountSat : UInt64
  sequence : UInt32
  hashOutputs : ByteArray
  locktime : UInt32
  sighashType : UInt32

def Bip143Preimage.preimageBytes (p : Bip143Preimage) : ByteArray :=
  exactU32 p.version ++ p.hashPrevouts ++ p.hashSequence ++
    p.outpointTxid ++ exactU32 p.outpointIndex ++
    exactCS p.scriptCode.size ++ p.scriptCode ++
    exactU64 p.amountSat ++ exactU32 p.sequence ++
    p.hashOutputs ++ exactU32 p.locktime ++ exactU32 p.sighashType

theorem Bip143Preimage.preimageBytes_size (p : Bip143Preimage)
    (hp : p.hashPrevouts.size = 32) (hq : p.hashSequence.size = 32)
    (ho : p.outpointTxid.size = 32) (hh : p.hashOutputs.size = 32) :
    p.preimageBytes.size =
      156 + compactSizeWidth p.scriptCode.size + p.scriptCode.size

def exactSighashDigest (M : PrimitiveModel) (p : Bip143Preimage) : ByteArray :=
  M.sha256 (M.sha256 p.preimageBytes)

theorem exactSighashDigest_size (M : PrimitiveModel) (p : Bip143Preimage) :
    (exactSighashDigest M p).size = 32
```

Field order is exactly BIP 143's ten fields: version, `hashPrevouts`,
`hashSequence`, outpoint, `scriptCode`, amount, `nSequence`, `hashOutputs`,
`nLockTime`, `hashType`. The fixed width is 156 bytes before the CompactSize
prefix and script bytes.

A concrete vector is `decide`-checked:

```lean
def vectorPreimage : Bip143Preimage
-- version 2, 32×0xaa/0xbb/0xcc/0xdd sub-hashes, index 0,
-- scriptCode [0x51], amount 1000, sequence 0xffffffff,
-- locktime 0x20000000, sighashType 1

theorem vectorPreimage_bytes :
    Bitcoin.Serialization.bL vectorPreimage.preimageBytes =
      [0x02, 0x00, 0x00, 0x00] ++ List.replicate 32 0xaa ++
      List.replicate 32 0xbb ++ List.replicate 32 0xcc ++
      [0x00, 0x00, 0x00, 0x00, 0x01, 0x51,
       0xe8, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
       0xff, 0xff, 0xff, 0xff] ++
      List.replicate 32 0xdd ++
      [0x00, 0x00, 0x00, 0x20, 0x01, 0x00, 0x00, 0x00]

theorem vectorPreimage_size :
    (Bitcoin.Serialization.bL vectorPreimage.preimageBytes).length = 158
```

### 3.5 HTLC second-stage transaction layout

```lean
structure HtlcWire where
  version : UInt32
  commitmentTxid : ByteArray
  commitmentOutputIndex : UInt32
  sequence : UInt32
  valueSat : UInt64
  scriptPubKey : ByteArray
  locktime : UInt32

def HtlcWire.toTx (h : HtlcWire) : Bitcoin.Data.Tx
def HtlcWire.txBytes (h : HtlcWire) : ByteArray := Bitcoin.Data.serTx h.toTx

def HtlcWire.WellFormed (h : HtlcWire) : Prop :=
  h.commitmentTxid.size = 32 ∧
  h.scriptPubKey.size ≤ Bitcoin.Serialization.MAX_SIZE ∧
  h.valueSat < 9223372036854775808

theorem HtlcWire.wireDomain_toTx (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.wireDomain h.toTx

theorem HtlcWire.txBytes_parse (h : HtlcWire) (hw : h.WellFormed) :
    Bitcoin.Serialization.decTxCore (Bitcoin.Serialization.bL h.txBytes) =
      .ok (h.toTx, [])

theorem HtlcWire.txBytes_size (h : HtlcWire) :
    h.txBytes.size =
      4 + 1 + h.commitmentTxid.size + 4 + 1 + 4 + 1 +
        8 + compactSizeWidth h.scriptPubKey.size + h.scriptPubKey.size + 4
```

The HTLC layout has one input spending the commitment output and one output
with the supplied satoshi value and `scriptPubKey`. The transaction is again
serialized and parsed by the vendored code, so it is bit-exact relative to the
vendored `Tx` model.

### 3.6 Structural refinement of `commitmentPreimage`

```lean
structure CommitmentMeta where
  commitmentNumber : Nat
  obscuredCommitmentNumber : Nat
  fundingValueSat : Nat
  fundingScript : ByteArray
  holder : Direction
  toLocalSat : Nat
  toRemoteSat : Nat
  feeSat : Nat
  contestDelay : Nat
  anchorOutputs : Bool
  feeratePerKw : Nat
  htlcs : List HtlcSighashView

def viewOfWire (w : CommitmentWire) (m : CommitmentMeta) : CommitmentSighashView

@[simp] theorem viewOfWire_fundingTxid ...
@[simp] theorem viewOfWire_fundingOutputIndex ...
@[simp] theorem viewOfWire_outputs ...
@[simp] theorem viewOfWire_commitmentNumber ...
@[simp] theorem viewOfWire_htlcs ...

def obscuredOfWire (w : CommitmentWire) : Nat :=
  (w.sequence.toNat % 2 ^ 24) * 2 ^ 24 + (w.locktime.toNat % 2 ^ 24)

def Obscures (w : CommitmentWire) (m : CommitmentMeta) : Prop :=
  m.obscuredCommitmentNumber < 2 ^ 48 ∧
  w.locktime.toNat = 0x20000000 + (m.obscuredCommitmentNumber % 2 ^ 24) ∧
  w.sequence.toNat = 0x80000000 + ((m.obscuredCommitmentNumber / 2 ^ 24) % 2 ^ 24)

theorem obscuredOfWire_eq_of_obscures ... :
    obscuredOfWire w = m.obscuredCommitmentNumber % 2 ^ 48

theorem viewOfWire_obscured ... (h : Obscures w m) :
    (viewOfWire w m).obscuredCommitmentNumber = obscuredOfWire w

def SharedEq (w₁ w₂ : CommitmentWire) : Prop :=
  w₁.fundingTxid = w₂.fundingTxid ∧
  w₁.fundingOutputIndex = w₂.fundingOutputIndex ∧
  w₁.outputs.map (fun o => o.output) = w₂.outputs.map (fun o => o.output)

theorem viewOfWire_eq_of_shared ... (h : SharedEq w₁ w₂) :
    viewOfWire w₁ m = viewOfWire w₂ m

theorem commitmentPreimage_eq_of_shared ... (h : SharedEq w₁ w₂) :
    commitmentPreimage (viewOfWire w₁ m) = commitmentPreimage (viewOfWire w₂ m)

theorem commitmentDigest_eq_of_shared (M : PrimitiveModel) ... (h : SharedEq w₁ w₂) :
    commitmentDigest M (viewOfWire w₁ m) = commitmentDigest M (viewOfWire w₂ m)
```

This is the positive refinement statement: the structural serializer is a
function of the wire fields it claims to model (funding txid/index, output
values, and — under `Obscures` — the 48-bit obscured commitment number), so
equal modelled wire data yields identical structural preimages and digests.

The abstraction is proved strict by a concrete counterexample:

```lean
def vectorWireShortScript : CommitmentWire :=
  { vectorWire with
    outputs := [{ vectorOutput1 with scriptPubKey := byteList [0x51] },
      vectorOutput2] }

theorem vectorView_eq :
    viewOfWire vectorWire vectorMeta =
      viewOfWire vectorWireShortScript vectorMeta

theorem structuralView_not_determine_scripts :
    ∃ (w₁ w₂ : CommitmentWire) (m : CommitmentMeta),
      viewOfWire w₁ m = viewOfWire w₂ m ∧ w₁.txBytes ≠ w₂.txBytes
```

The proof changes only the first output's `scriptPubKey` from the 22-byte
P2WPKH program to a one-byte script. `viewOfWire` is unchanged because it maps
`ExactCommitmentOutput.output` and ignores `scriptPubKey`; `txBytes` differs
because `txBytes_size` is strictly smaller. This is the mechanised statement
that the structural serializer **drops output scripts** and therefore is a
refinement of, not equal to, the exact wire layout.

## 4. Build result

### 4.1 Real shared tree — blocked before reaching the owned module

Command (as required):

```bash
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.SighashTargets
```

Result:

```text
✖ [18/35] Building LnLean.Proofs.Conservation (1.2s)
error: LnLean/Proofs/Conservation.lean:649:68: Application type mismatch: ...
error: LnLean/Proofs/Conservation.lean:645:23: unsolved goals
error: build failed
```

`SighashTargets` imports `LnLean.Proofs.Conservation` (line 92), so the owned
module is never elaborated in the real tree. This is a concurrent-lane break,
not a failure of this lane's code; see §8.

### 4.2 Validation copy — succeeds

In `/tmp/opencode/s6-bitexact` (a full copy of the tree with only the
`Conservation.lean` `LawfulBEq` patch shown in §8 applied), the same command
succeeds:

```text
✔ [35/35] Built LnLean.Proofs.Channel.SighashTargets (2.0s)
Build completed successfully (35 jobs).
```

The file built there is byte-for-byte the file now in the real tree
(`cp` from the real tree before the build). Thus the 490-line addition is
elaborated end-to-end, including its dependency on `Conservation` after the
one-instance repair.

## 5. Axiom audit

Run in the validation copy with `lake env lean AxiomsBitExact.lean` over
`#print axioms` for every significant new declaration. Representative output:

```text
exactU32_size                         [propext]
exactU64_size                         [propext]
compactSizeEnc_size                   [propext, Quot.sound]
foldl_append_size                     [propext, Quot.sound]
CommitmentWire.wireDomain_toTx         [propext, Quot.sound]
CommitmentWire.txBytes_parse           [propext, Quot.sound]
CommitmentWire.txBytes_size            [propext, Quot.sound]
vectorCommitmentTx                     [propext]
vectorCommitmentTx_size                [propext]
Bip143Preimage.preimageBytes_size      [propext, Quot.sound]
vectorPreimage_bytes                   [propext]
vectorPreimage_size                    [propext]
exactSighashDigest_size                [propext]
HtlcWire.wireDomain_toTx               [propext, Quot.sound]
HtlcWire.txBytes_parse                 [propext, Quot.sound]
HtlcWire.txBytes_size                  [propext, Quot.sound]
viewOfWire_fundingTxid                 (none)
viewOfWire_outputs                     (none)
obscuredOfWire_eq_of_obscures          [propext, Quot.sound]
viewOfWire_obscured                    [propext, Quot.sound]
commitmentPreimage_eq_of_shared        [propext]
commitmentDigest_eq_of_shared          [propext]
structuralView_not_determine_scripts   [propext, Quot.sound]
```

The union is exactly the permitted set `{propext, Quot.sound,
Classical.choice}`; `Classical.choice` does not occur. No audit of the
pre-existing declarations was repeated, since they were not modified.

## 6. Forbidden-construct scan

```bash
grep -nE '\b(sorry|admit|native_decide|unsafe)\b|@\[implemented_by\]|^axiom |\baxiom [A-Za-z]' \
  LnLean/Proofs/Channel/SighashTargets.lean
```

Result: no matches. `decide` is used only for concrete closed vectors; the
kernel still checks the resulting proof term, so this is ordinary `decide`, not
`native_decide`.

## 7. Scope, boundaries, and honest caveats

The lane delivers the exact *layout* for the modelled fields, not a
consensus-validity theorem. The following boundaries remain and are deliberately
not hidden:

1. **Byte order / txids.** `fundingTxid` and `outpointTxid` are taken as the
   already-serialized 32-byte consensus-internal values. No display-order
   reversal, RPC hex conversion, or `GetHex` theorem is modelled.
2. **Sub-hashes.** `hashPrevouts`, `hashSequence`, and `hashOutputs` are
   explicit 32-byte inputs. This module proves their width, not their
   derivation. `LnLean/Bitcoin/Sighash.lean` (lane `S6-L1-SIGHASH`) has
   `ofTx`/`bL_encode_ofTx` for the derivation; convergence is listed in §9.
3. **`scriptCode`.** Supplied raw and CompactSize-prefixed. No witness-program
   reconstruction, P2WPKH/P2WSH scriptCode synthesis, `OP_CODESEPARATOR`
   handling, or `FindAndDelete` behaviour is modelled.
4. **`sighashType`.** Serialized as the raw `UInt32`. `SIGHASH_SINGLE` /
   `ANYONECANPAY` zero-sub-hash semantics and the out-of-range `SIGHASH_SINGLE`
   rule are not re-proved here.
5. **Witness.** `CommitmentWire.toTx` and `HtlcWire.toTx` use
   `witness := [[]]`; `hasWitness` is proved false and the vendored
   serialization is the non-witness serialization. Signature/witness stacks are
   not modelled. This is the correct unsigned transaction form for a sighash
   preimage, but it is not a broadcast-ready transaction.
6. **Commitment-number derivation.** `Obscures` states the BOLT 3 bit layout
   (`nLockTime = 0x20000000 | low24`, `nSequence = 0x80000000 | high24`) and
   recovers the 48-bit obscured value. The obscurer itself (basepoint/seed
   derivation) and the commitment-number counter are metadata, not derived.
7. **Output ordering and scripts.** `outputs` is caller-supplied in order; the
   BOLT 3 canonical ordering (`to_local`, `to_remote`, anchors, HTLCs) is not
   enforced. Each `scriptPubKey` is explicit bytes; only its size is bounded.
8. **Fees and conservation.** `CommitmentMeta.feeSat` is metadata; this module
   does not prove that inputs cover outputs plus fee. `HtlcWire.valueSat` has no
   linked second-stage fee field beyond the implicit difference.
9. **HTLC structural bridge.** The negative/positive refinement results are
   stated for `commitmentPreimage`/`viewOfWire`. The existing
   `htlcPreimage` is not yet bridged field-by-field to `HtlcWire`; the HTLC side
   here establishes the wire layout and parser round-trip only.
10. **Hash floor.** `exactSighashDigest M p` is
    `M.sha256 (M.sha256 p.preimageBytes)` under the `PrimitiveModel` hash
    abstraction. No theorem identifies this with the vendored seam
    `Bitcoin.Crypto.Seam.sha256d`, and `commitmentDigest` additionally prepends
    `commitmentTag`; the two digest constructions are intentionally different.
11. **No consensus claim.** Nothing here proves script validity, signature
    validity, malleability resistance, or that a real node would accept a spend.
    The BIP 143 preimage is not proved byte-equal to
    `Bitcoin.SigHash.bip143MsgL` or to `LnLean.Bitcoin.Sighash.encode` in this
    lane; the concrete vector and size theorem pin the layout, but the
    cross-module equality is follow-up work (§9).
12. **Parser domain.** `wireDomain` hypotheses are explicit (32-byte txid,
    in-range CompactSize lengths, non-negative and `< 2^63` output values).
    Scripts are bounded by `MAX_SIZE`; other vendored domain conditions are
    discharged in `wireDomain_toTx`.

## 8. Integration blocker: `Conservation.lean`

The real tree fails because concurrent lane `S6-CH-TYPES` added
`netAmountSat` to `CommitmentHTLCOutput` in `LnLean/Channel/Types.lean`
(five fields now: `direction`, `amountSat`, `cltvExpiry`, `state`,
`netAmountSat`) but the `LawfulBEq CommitmentHTLCOutput` instance in
`LnLean/Proofs/Conservation.lean` still matches four fields.

Exact error:

```text
error: LnLean/Proofs/Conservation.lean:649:68: Application type mismatch:
  hsa has type instBEqHTLCState.beq sa sb = true ∧ netAmountSat✝¹ = netAmountSat✝
  but is expected to have type (sa == sb) = true
error: LnLean/Proofs/Conservation.lean:645:23: unsolved goals
```

Minimal repair (validated in the copy; **not applied to the real tree** because
`Conservation.lean` is not owned by this lane):

```diff
--- a/LnLean/Proofs/Conservation.lean
+++ b/LnLean/Proofs/Conservation.lean
@@ -640,18 +640,18 @@
   eq_of_beq := by
     intro a b h
     cases a with
-    | mk da aa ca sa =>
+    | mk da aa ca sa na =>
       cases b with
-      | mk db ab cb sb =>
+      | mk db ab cb sb nb =>
         simp [BEq.beq, instBEqCommitmentHTLCOutput.beq] at h
-        rcases h with ⟨hda, haa, hca, hsa⟩
+        rcases h with ⟨hda, haa, hca, hsa, hna⟩
         have hda' : da = db := LawfulBEq.eq_of_beq (α := Direction) hda
         have hsa' : sa = sb := LawfulBEq.eq_of_beq (α := HTLCState) hsa
-        rw [hda', haa, hca, hsa']
+        rw [hda', haa, hca, hsa', hna]
   rfl := by
     intro a
     cases a with
-    | mk d am c s =>
+    | mk d am c s n =>
       have hd : instBEqDirection.beq d d = true := by cases d <;> rfl
       have hs : instBEqHTLCState.beq s s = true := by cases s <;> rfl
       simp [BEq.beq, instBEqCommitmentHTLCOutput.beq, hd, hs]
```

Owner review should also confirm whether `htlcOutputsValue` (and any amount
bound in `Conservation.lean`) should sum `netAmountSat` rather than
`amountSat`; the two-hunk patch above only restores the `BEq` instance arity so
the tree can build.

## 9. Integration steps for the parent

1. Apply the `Conservation.lean` repair in §8 (or have the `S6-CH-TYPES`
   owner do it), and confirm the intended semantics of `netAmountSat` in the
   conservation amount lemmas.
2. Re-run the locked build:
   ```bash
   cd /home/ubuntu/ln-lean-repair
   LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
     lake build LnLean.Proofs.Channel.SighashTargets
   ```
   Expected: `[35/35] Built ...`, matching §4.2.
3. Re-run the axiom audit against the real tree:
   ```bash
   cd /home/ubuntu/ln-lean-repair
   lake env lean /tmp/opencode/s6-bitexact/AxiomsBitExact.lean
   ```
   (The scratch audit file only imports the module and prints axioms; it is not
   part of the repository.)
4. Optional follow-up (not required for this lane): converge the duplicated
   BIP 143 layout with `LnLean/Bitcoin/Sighash.lean` by proving
   `bL p.preimageBytes = bL (encode (toPreimage p))`, or by replacing
   `Bip143Preimage` with that module's `Preimage`/`ofTx`. This would connect
   `hashPrevouts`/`hashSequence`/`hashOutputs` derivation and the seam digest,
   and should be done only after both lanes' files are stable.
5. No change to `LnLean.lean`, `Obligations.lean`, `Traceability.lean`, or
   `AxiomAudit.lean` is needed: the module is already in the import graph and
   the additions are ordinary declarations in its existing namespace.

## 10. Blockers

- **P0 for real-tree verification:** `LnLean/Proofs/Conservation.lean` does not
  compile after `CommitmentHTLCOutput.netAmountSat` was added. The owned module
  is blocked transitively (it imports `Conservation`). Patch in §8.
- No blocker in the owned module: the exact same content builds to `[35/35]`
  in the repaired copy, with the permitted axiom set and a clean forbidden-token
  scan.
- No Git operation was performed, so the change is staged only in the working
  tree as a normal file modification.

## 11. Summary for the parent

- Added §12 to `LnLean/Proofs/Channel/SighashTargets.lean` (+490 lines):
  `CommitmentWire`/`HtlcWire` exact transaction layouts using vendored
  `serTx`, `Bip143Preimage` exact 10-field preimage, parser round-trips,
  size formulas, concrete 125-byte commitment and 158-byte preimage vectors.
- Proved the existing structural serializer is refined by the wire:
  `SharedEq → commitmentPreimage/commitmentDigest` equality, plus
  `Obscures` recovering the 48-bit obscured commitment number.
- Mechanised the strictness of the abstraction:
  `structuralView_not_determine_scripts` shows that dropping output
  `scriptPubKey`s changes wire bytes while preserving the structural view.
- Validation: real tree currently fails at `LnLean.Proofs.Conservation`
  (concurrent `netAmountSat` field); the same owned file builds `[35/35]` in a
  copy with the two-hunk `LawfulBEq` repair. Axioms are exactly
  `{propext, Quot.sound}` (no `Classical.choice` in the new declarations);
  forbidden-token scan is empty.
- Action needed from parent/owner: apply the `Conservation.lean` patch, then
  re-run the locked build. No claim of bit-exact consensus is made; §7 lists
  every remaining boundary, including the unproved equality to the vendored
  BIP 143 serializer.
