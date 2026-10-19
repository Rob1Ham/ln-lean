# S8-PR-HTLCPREIMAGE — exact HTLC second-stage BIP 143 preimage bytes

**Lane:** `S8-PR-HTLCPREIMAGE` (`PR-05`, `PR-02`).
**Worktree:** `/home/ubuntu/ln-lean-repair`.
**Verdict:** **target met for the modelled HTLC wires and synthesized
scriptCodes.** For every `HtlcWire`, every `scriptCode` byte string, every
hashtype and every `UInt64` amount, the exact-wire HTLC preimage is proved
byte-equal to the vendored `Bitcoin.SigHash.bip143MsgL`, and the
`HtlcSpend` instantiation synthesizes the BOLT 3 HTLC-success / HTLC-timeout
`scriptCode` from the anchor-variant witness-script templates. The
arbitrary-preimage field-agreement form is retained with its eight explicit
hypotheses. No `sorry`/`axiom`/`admit`/`native_decide`/`unsafe`/
`@[implemented_by]` was introduced; the axiom set is exactly
`{propext, Quot.sound, Classical.choice}`.

- Owned files touched:
  - **new** `LnLean/Proofs/Channel/HtlcPreimageTargets.lean` (974 lines);
  - `agents/reports/swarm8/S8-PR-HTLCPREIMAGE.md` — this report.
- Not modified by this lane: `SighashTargets.lean`, `LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`, shared docs,
  other lanes' files, vendor sources.
- No Git write. The changes are working-tree files only.

## 1. Result in one paragraph

`htlcBip143Preimage h scriptCode ht amountSat` is defined as
`Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat`; the requested equality
is then the wave-7 transaction-derived theorem
`Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx`. No field is assumed: the
wire's version, three sub-hashes, outpoint txid (internal order), outpoint
index, sequence, locktime, amount and hashtype all come from the modelled
`HtlcWire.toTx` / `ofTx`. A second theorem transfers equality to the digest
through the vendored `signatureHashBip143Impl`. The arbitrary-preimage form
`htlc_arbitrary_preimage_field_agreement` keeps the eight field-agreement
hypotheses visible. `HtlcSpend` then instantiates the construction for the
HTLC-success and HTLC-timeout second-stage transactions: the success
`scriptCode` is the 143-byte `receivedHtlcWitnessScript`, the timeout
`scriptCode` is the 136-byte `offeredHtlcWitnessScript`, with exact preimage
sizes 300 and 293 bytes. Two `decide` vectors pin the field boundaries
(including the one-byte CompactSize prefixes `0x8f` / `0x88`), and display-order
txid conversion is modelled by byte reversal, with the offset-68 slice proved
to be the **internal-order** txid. `Seam.htlcBranchScript` is proved not to be
any of the BOLT 3 scripts (wrong prefix and CLTV truncation), so the faithful
scripts are the ones used for `scriptCode`.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Proofs/Channel/HtlcPreimageTargets.lean` | New module: exact HTLC preimage, `toPreimage` bridge, digest transfer, arbitrary-preimage refinement, display-order txid section, `HtlcSpend` scriptCode synthesis, P2WSH shape theorems, four negative `htlcBranchScript` theorems, vectors, summary theorem. |
| `agents/reports/swarm8/S8-PR-HTLCPREIMAGE.md` | This report. |

No pre-existing declaration in `SighashTargets.lean` §12/§13 was changed or
removed. The new module only imports
`LnLean.Proofs.Channel.SighashTargets` and
`LnLean.Proofs.Bitcoin.ScriptProps`.

## 3. Exact signatures

All names below are in
`namespace LnLean.Proofs.Channel.HtlcPreimageTargets` unless qualified.
`bL : ByteArray → List UInt8` is `Bitcoin.Serialization.bL`.

### 3.1 The target byte equality

```lean
def htlcBip143Preimage (h : HtlcWire) (scriptCode : ByteArray) (ht : UInt32)
    (amountSat : UInt64) : Bip143Preimage :=
  Bip143Preimage.ofTx h.toTx 0 scriptCode ht amountSat

theorem htlcBip143Preimage_eq_bip143MsgL (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int) :=
  Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx h.toTx 0 scriptCode ht amountSat
```

This is the requested statement with `amount := (amountSat.toNat : Int)`, the
same lift used by `Bip143Preimage.ofTx` and the vendored encoder. It has **no
hypotheses**.

`ByteArray`-level form against the model encoder:

```lean
theorem htlcBip143Preimage_bytes_eq_encode (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes =
      LnLean.Bitcoin.Sighash.encode
        (LnLean.Bitcoin.Sighash.ofTx h.toTx 0 scriptCode ht
          (amountSat.toNat : Int))
```

### 3.2 `ofTx` / `toPreimage` bridge and digest

```lean
theorem htlcBip143Preimage_toPreimage (h : HtlcWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.ofTx h.toTx 0 scriptCode ht
        (amountSat.toNat : Int)

theorem htlcBip143Preimage_digest_eq_sighashWitnessV0 (h : HtlcWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    LnLean.Bitcoin.Sighash.digest
        (htlcBip143Preimage h scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int)
```

`HtlcWire.toTx` has exactly one input, so the signing input index is `0`; the
digest theorem discharges the in-range side condition by `simp [HtlcWire.toTx]`.

Field projections (all `rfl`) tie the preimage to the wire without any reversal:

```lean
htlcBip143Preimage_version, htlcBip143Preimage_outpointTxid,
htlcBip143Preimage_outpointIndex, htlcBip143Preimage_sequence,
htlcBip143Preimage_locktime, htlcBip143Preimage_amountSat,
htlcBip143Preimage_sighashType
htlcBip143Preimage_wire_fields   -- bundled conjunction of the above
```

### 3.3 Arbitrary-preimage form (retained)

```lean
theorem htlc_arbitrary_preimage_field_agreement (p : Bip143Preimage) (h : HtlcWire)
    (amount : Bitcoin.Data.Amount)
    (hversion : p.version = h.version)
    (hprev : bL p.hashPrevouts =
      Bitcoin.SigHash.hashPrevoutsL h.toTx p.sighashType)
    (hseq : bL p.hashSequence =
      Bitcoin.SigHash.hashSequenceL h.toTx p.sighashType)
    (houtpoint : p.outpointTxid = h.commitmentTxid ∧
      p.outpointIndex = h.commitmentOutputIndex)
    (hseq2 : p.sequence = h.sequence)
    (hout : bL p.hashOutputs =
      Bitcoin.SigHash.hashOutputsL h.toTx 0 p.sighashType)
    (hlock : p.locktime = h.locktime)
    (hamount : (p.amountSat.toNat : Int) = amount) :
    bL p.preimageBytes =
      Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL p.scriptCode) p.sighashType amount
```

The eight hypotheses are exactly the field-agreement context of
`LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL`; the transaction-derived form
discharges all of them by construction.

### 3.4 Display-order txid conversion

```lean
def reverseBytes (b : ByteArray) : ByteArray := byteList (bL b).reverse
def displayTxid (internal : ByteArray) : ByteArray := reverseBytes internal
def internalTxid (display : ByteArray) : ByteArray := reverseBytes display

theorem reverseBytes_involutive, internalTxid_displayTxid,
  displayTxid_internalTxid, reverseBytes_size, displayTxid_size,
  internalTxid_size

theorem preimageBytes_drop68_take32 (p : Bip143Preimage)
    (hp : p.hashPrevouts.size = 32) (hq : p.hashSequence.size = 32)
    (ho : p.outpointTxid.size = 32) :
    ((bL p.preimageBytes).drop 68).take 32 = bL p.outpointTxid

theorem preimageBytes_drop100_take4 (p : Bip143Preimage) … :
    ((bL p.preimageBytes).drop 100).take 4 =
      Bitcoin.SigHash.serU32L p.outpointIndex

theorem htlcBip143Preimage_outpoint_bytes (h : HtlcWire) … (htx : h.commitmentTxid.size = 32) :
    ((bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes).drop 68).take
        32 = bL h.commitmentTxid

theorem htlcBip143MsgL_outpoint_bytes (h : HtlcWire) … :
    ((Bitcoin.SigHash.bip143MsgL h.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int)).drop 68).take 32 = bL h.commitmentTxid

theorem htlcBip143Preimage_outpoint_of_display_txid (h : HtlcWire) …
    (hexTxid : ByteArray) (hsize : hexTxid.size = 32)
    (hdisplay : h.commitmentTxid = displayTxid hexTxid) :
    ((bL (htlcBip143Preimage h scriptCode ht amountSat).preimageBytes).drop 68).take
        32 = (bL hexTxid).reverse

theorem displayTxid_not_identity_witness :
    displayTxid vectorAsymmetricTxid ≠ vectorAsymmetricTxid
```

The preimage inserts the txid **verbatim in consensus-internal order**. A caller
holding RPC/display hex must assign `commitmentTxid := internalTxid hexTxid`
(equivalently, the offset-68 bytes are `(bL hexTxid).reverse`).

### 3.5 `HtlcSpend` and scriptCode synthesis

```lean
structure HtlcSpend where
  commitmentTxid : ByteArray          -- internal order
  commitmentOutputIndex : UInt32
  anchorOutputs : Bool                -- nSequence 1 vs 0
  revocationKeyHash160 : ByteArray    -- 20-byte RIPEMD160(SHA256(revocationpubkey)) image
  paymentHash160 : ByteArray          -- 20-byte RIPEMD160(payment_hash) image
  remoteHtlcKey : PubKey              -- 33-byte compressed
  localHtlcKey : PubKey               -- 33-byte compressed
  cltvExpiry : UInt32
  amountSat : UInt64                  -- gross HTLC value
  secondStageFeeSat : Nat
  outputScriptPubKey : ByteArray

def HtlcSpend.WellFormed (s : HtlcSpend) : Prop :=
  s.commitmentTxid.size = 32 ∧ s.revocationKeyHash160.size = 20 ∧
  s.paymentHash160.size = 20 ∧ s.remoteHtlcKey.bytes.size = 33 ∧
  s.localHtlcKey.bytes.size = 33 ∧
  s.secondStageFeeSat ≤ s.amountSat.toNat

def HtlcSpend.successWire  (s) : HtlcWire  -- version 2, locktime 0
def HtlcSpend.timeoutWire  (s) : HtlcWire  -- version 2, locktime = cltvExpiry
def HtlcSpend.successScriptCode (s) : ByteArray :=
  (receivedHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
    s.remoteHtlcKey s.localHtlcKey s.cltvExpiry.toNat).bytes
def HtlcSpend.timeoutScriptCode (s) : ByteArray :=
  (offeredHtlcWitnessScript s.revocationKeyHash160 s.paymentHash160
    s.remoteHtlcKey s.localHtlcKey).bytes
def HtlcSpend.successPreimage (s) (ht) : Bip143Preimage
def HtlcSpend.timeoutPreimage (s) (ht) : Bip143Preimage
```

The exact instantiated statements are:

```lean
theorem HtlcSpend.successScriptCode_is_received (s) :
    s.successScriptCode = (receivedHtlcWitnessScript …).bytes   -- rfl

theorem HtlcSpend.timeoutScriptCode_is_offered (s) :
    s.timeoutScriptCode = (offeredHtlcWitnessScript …).bytes     -- rfl

theorem HtlcSpend.successPreimage_eq_bip143MsgL (s) (ht) :
    bL (s.successPreimage ht).preimageBytes =
      Bitcoin.SigHash.bip143MsgL s.successWire.toTx 0
        (bL s.successScriptCode) ht (s.amountSat.toNat : Int)

theorem HtlcSpend.timeoutPreimage_eq_bip143MsgL (s) (ht) :
    bL (s.timeoutPreimage ht).preimageBytes =
      Bitcoin.SigHash.bip143MsgL s.timeoutWire.toTx 0
        (bL s.timeoutScriptCode) ht (s.amountSat.toNat : Int)

theorem HtlcSpend.successPreimage_digest_eq_sighashWitnessV0 (s) (ht) :
    LnLean.Bitcoin.Sighash.digest (s.successPreimage ht).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl s.successWire.toTx 0
        (bL s.successScriptCode) ht (s.amountSat.toNat : Int)
-- and the timeout analogue

theorem HtlcSpend.successScriptCode_size (s) (hw : s.WellFormed) :
    s.successScriptCode.size = 143
theorem HtlcSpend.timeoutScriptCode_size (s) (hw : s.WellFormed) :
    s.timeoutScriptCode.size = 136
theorem HtlcSpend.successPreimage_size (s) (hw) (ht) :
    (s.successPreimage ht).preimageBytes.size = 300
theorem HtlcSpend.timeoutPreimage_size (s) (hw) (ht) :
    (s.timeoutPreimage ht).preimageBytes.size = 293
```

`successScriptCode_size_ok` / `timeoutScriptCode_size_ok` prove the vendored
`witnessScriptSizeOk` predicate for both scripts.

The P2WSH output shape is conditional only on the hash image:

```lean
theorem HtlcSpend.successOutput_is_p2wsh (s) (M : LnLean.Crypto.PrimitiveModel)
    (hout : s.outputScriptPubKey = (p2wsh (M.sha256 s.successScriptCode)).bytes) :
    s.outputScriptPubKey.size = 34
-- and the timeout analogue
```

No SHA-256 is recomputed and no hash-image relation is assumed beyond the
explicit equation.

### 3.6 `Seam.htlcBranchScript` is rejected

```lean
theorem htlcBranchScript_take2 … :
    (bL (htlcBranchScript ph cltv pk).bytes).take 2 = [OP_IF, OP_HASH160]
theorem offeredHtlcWitnessScript_take2 … :
    (bL (offeredHtlcWitnessScript …).bytes).take 2 = [OP_DUP, OP_HASH160]
theorem receivedHtlcWitnessScript_take2 … :
    (bL (receivedHtlcWitnessScript …).bytes).take 2 = [OP_DUP, OP_HASH160]
theorem toLocalScriptFull_take2 … (hr : revocationKey.bytes.size = 33) :
    (bL (toLocalScriptFull …).bytes).take 2 = [OP_IF, 0x21]

theorem htlcBranchScript_ne_offeredHtlcWitnessScript …
theorem htlcBranchScript_ne_receivedHtlcWitnessScript …
theorem htlcBranchScript_ne_toLocalScriptFull …
theorem htlcBranchScript_cltv_not_injective (ph) (pk) :
    htlcBranchScript ph 0 pk = htlcBranchScript ph 256 pk
```

The last theorem records that `cltv.toUInt8` truncates modulo 256, so the stub
cannot encode a BOLT 3 `CScriptNum` CLTV value.

### 3.7 Byte-layout vectors

The vector uses `SIGHASH_NONE|ANYONECANPAY` (`0x82`), so all three BIP 143
sub-hashes are the zero vector and `decide` checks byte order and field
boundaries without evaluating SHA-256. It uses a 32-byte non-palindromic
commitment txid, 20-byte hash images, 33-byte keys, anchor `nSequence = 1`,
amount 7000 sat, fee 3515 sat and `cltvExpiry = 500000`.

| field | success offset | timeout offset | bytes |
|---|---:|---:|---|
| version | 0 | 0 | `02 00 00 00` |
| `hashPrevouts` | 4 | 4 | zero vector |
| `hashSequence` | 36 | 36 | zero vector |
| outpoint txid (internal) | 68 | 68 | `vectorHtlcCommitmentTxid` |
| outpoint index | 100 | 100 | `01 00 00 00` |
| CompactSize(`scriptCode`) | 104 (1 byte) | 104 (1 byte) | `8f` / `88` |
| `scriptCode` | 105 | 105 | 143 / 136 bytes |
| amount | 248 | 241 | `58 1b 00 00 00 00 00 00` |
| `nSequence` | 256 | 249 | `01 00 00 00` |
| `hashOutputs` | 260 | 253 | zero vector |
| `nLockTime` | 292 | 285 | `00…` / `20 a1 07 00` |
| sighash type | 296 | 289 | `82 00 00 00` |
| **total** | **300** | **293** | |

Theorems: `vectorHtlcSpend_wellFormed`,
`vectorHtlcSpend_success_bytes_layout`,
`vectorHtlcSpend_timeout_bytes_layout`,
`vectorHtlcSpend_successScriptCode_slice` (`drop 105`, take 143),
`vectorHtlcSpend_timeoutScriptCode_slice` (`drop 105`, take 136),
`vectorHtlcSpend_success_vendor_scriptCode_slice`,
`vectorHtlcSpend_timeout_vendor_scriptCode_slice`,
`vectorHtlcSpend_commitmentTxid_not_palindromic`,
`vectorHtlcSpend_outpoint_display`, and the two size theorems
(`300`, `293`). The vendor-slice theorems rewrite with
`← HtlcSpend.successPreimage_eq_bip143MsgL` /
`← HtlcSpend.timeoutPreimage_eq_bip143MsgL`, so the same offsets are checked in
the vendored encoder as in the model preimage.

### 3.8 Bundled summary

```lean
theorem htlc_preimage_target_summary (s : HtlcSpend) (hw : s.WellFormed) (ht : UInt32) :
    bL (s.successPreimage ht).preimageBytes =
        Bitcoin.SigHash.bip143MsgL s.successWire.toTx 0
          (bL s.successScriptCode) ht (s.amountSat.toNat : Int) ∧
      bL (s.timeoutPreimage ht).preimageBytes =
        Bitcoin.SigHash.bip143MsgL s.timeoutWire.toTx 0
          (bL s.timeoutScriptCode) ht (s.amountSat.toNat : Int) ∧
      (s.successPreimage ht).toPreimage =
        LnLean.Bitcoin.Sighash.ofTx s.successWire.toTx 0 s.successScriptCode ht
          (s.amountSat.toNat : Int) ∧
      s.successScriptCode.size = 143 ∧
      s.timeoutScriptCode.size = 136 ∧
      s.successWire.locktime = 0 ∧
      s.timeoutWire.locktime = s.cltvExpiry
```

## 4. Build result

Final shared-tree build, under the shared build lock:

```bash
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Proofs.Channel.HtlcPreimageTargets
```

Result:

```text
✔ [50/50] Built LnLean.Proofs.Channel.HtlcPreimageTargets (1.9s)
Build completed successfully (50 jobs).  RC 0
```

The module also built `RC 0` (50 jobs) in a private validation tree at
`/tmp/opencode/htlc-check` constructed from `git archive HEAD` plus this new
file (vendor symlinked), which confirms the proof does not depend on any
concurrent lane's edits. During the lane the shared tree was transiently
unbuildable because `LnLean/Protocol/Handshake.lean` was mid-edit and its
`.olean` had been removed; that file was not touched here and the final run
above was taken after it settled. No full `lake build`, `collect-obligations.py`
or `collect-anchors.py` was run.

## 5. Axiom audit

Run in the shared tree with `lake env lean /tmp/opencode/SharedScratch.lean`
(scratch file outside the repository):

```text
htlcBip143Preimage_eq_bip143MsgL                    [propext, Classical.choice, Quot.sound]
htlcBip143Preimage_digest_eq_sighashWitnessV0       [propext, Classical.choice, Quot.sound]
htlc_arbitrary_preimage_field_agreement             [propext, Classical.choice, Quot.sound]
preimageBytes_drop68_take32                         [propext, Quot.sound]
preimageBytes_drop100_take4                         [propext, Quot.sound]
htlcBip143Preimage_outpoint_of_display_txid         [propext, Classical.choice, Quot.sound]
displayTxid_not_identity_witness                    [propext, Quot.sound]
HtlcSpend.successPreimage_eq_bip143MsgL             [propext, Classical.choice, Quot.sound]
HtlcSpend.timeoutPreimage_eq_bip143MsgL             [propext, Classical.choice, Quot.sound]
HtlcSpend.successPreimage_size                      [propext, Classical.choice, Quot.sound]
HtlcSpend.timeoutPreimage_size                      [propext, Classical.choice, Quot.sound]
htlcBranchScript_ne_offeredHtlcWitnessScript        [propext]
htlcBranchScript_ne_receivedHtlcWitnessScript       [propext]
htlcBranchScript_ne_toLocalScriptFull               [propext]
htlcBranchScript_cltv_not_injective                 [propext]
vectorHtlcSpend_timeout_bytes_layout                [propext, Classical.choice, Quot.sound]
vectorHtlcSpend_success_vendor_scriptCode_slice     [propext, Classical.choice, Quot.sound]
vectorHtlcSpend_timeout_vendor_scriptCode_slice     [propext, Classical.choice, Quot.sound]
vectorHtlcSpend_outpoint_display                    [propext, Classical.choice, Quot.sound]
htlc_preimage_target_summary                        [propext, Classical.choice, Quot.sound]
```

Union: exactly `{propext, Quot.sound, Classical.choice}`. No unlisted axiom.

## 6. Forbidden-construct scan

```bash
grep -nE '\b(sorry|admit|native_decide|unsafe)\b|@\[implemented_by\]|^axiom ' \
  LnLean/Proofs/Channel/HtlcPreimageTargets.lean
```

Result: no matches (exit 1). `decide` is used only on closed concrete vectors;
the kernel still checks the resulting proof term, so this is ordinary `decide`,
not `native_decide`.

## 7. Scope caveats

1. **Hash images are context, not computation.** `revocationKeyHash160` and
   `paymentHash160` are explicit 20-byte images. The model has no RIPEMD160
   bridge (`PrimitiveModel.hash160` is abstract HASH160), so
   `RIPEMD160(SHA256(revocationpubkey))` / `RIPEMD160(payment_hash)` are not
   recomputed. `WellFormed` only requires the lengths.
2. **`scriptCode` is an explicit byte string.** The generic equality
   `htlcBip143Preimage_eq_bip143MsgL` holds for **every** `scriptCode`; the
   `HtlcSpend` instantiation chooses the BOLT 3 witness script. P2WSH output
   shape is proved only under the explicit
   `outputScriptPubKey = p2wsh (M.sha256 scriptCode)` equation; no hash image or
   collision-resistance property is assumed.
3. **Anchor-variant templates.** `ScriptTemplates` contains only the
   anchor-variant offered/received HTLC witness scripts, and `HtlcSpend` uses
   those. `anchorOutputs` selects `nSequence = 1` vs `0` and the timeout
   locktime logic; it does **not** switch to a non-anchor HTLC script. The
   generic theorem is independent of this choice.
4. **Fixed-width CLTV push.** `receivedHtlcWitnessScript` uses the scaffold's
   fixed four-byte `pushScriptNum32`, not minimal `CScriptNum`. The 143-byte
   size and the offset table are for that fixed width. BOLT 3 minimal
   `CScriptNum` would give a different script for some `cltv_expiry` values.
5. **Txid is supplied, not derived.** `commitmentTxid` is a 32-byte
   internal-order input; this module does not recompute it as `SHA256d` of a
   `CommitmentWire`. Display-order conversion is explicitly `reverseBytes` /
   `displayTxid` / `internalTxid`; the offset-68 field is the internal-order
   value verbatim, never reversed.
6. **Amount model.** `amountSat : UInt64` is lifted to the signed vendor
   `Amount` by `(amountSat.toNat : Int)`. Negative `CAmount` values and Core's
   `amount ≥ 0` witness-v0 precondition are outside the `UInt64` model.
7. **No consensus/validity claim.** Signatures, fee sufficiency, script
   execution, P2WSH spends, transaction validity, mempool policy and node
   acceptance are not proved. `htlcBranchScript` negative results are
   structural facts about the Seam stub, not a consensus statement about BOLT 3
   execution.
8. **Transaction skeleton.** `HtlcWire.toTx` has exactly one input and one
   output; the signing index is therefore `0`. Multi-input HTLC transactions,
   `SIGHASH_SINGLE` out-of-range behaviour and `OP_CODESEPARATOR` /
   `FindAndDelete` are out of scope (BIP 143 P2WSH has no `FindAndDelete`).

## 8. Integration steps

1. **Compilation.** The shared working tree already contains
   `import LnLean.Proofs.Channel.HtlcPreimageTargets` in `LnLean.lean`
   (currently line 58). This lane did **not** edit `LnLean.lean`; if the parent
   reconstructs a clean tree from `HEAD` plus this lane's new file, add exactly:

   ```diff
   --- a/LnLean.lean
   +++ b/LnLean.lean
   @@ -55,6 +55,7 @@ import LnLean.Proofs.Channel.FeeTargets
    import LnLean.Proofs.Channel.HTLCProps
    import LnLean.Proofs.Channel.HtlcGlobalIdTargets
   +import LnLean.Proofs.Channel.HtlcPreimageTargets
    import LnLean.Proofs.Channel.PenaltyProps
   ```

2. **Do not add an import of this module to `SighashTargets.lean`.**
   `HtlcPreimageTargets` imports `SighashTargets`; the reverse import would
   create a cycle. The target theorem is available under the fully qualified
   name
   `LnLean.Proofs.Channel.HtlcPreimageTargets.htlcBip143Preimage_eq_bip143MsgL`.
   If the parent requires the theorem to live physically inside
   `SighashTargets.lean` §14, the mechanical move is to copy §1–§5 of the new
   file into `SighashTargets.lean` and delete the new module; that is a
   parent-owned refactor, not an additive import.
3. **Evidence update.** Record `PR-05` as closed for the HTLC second-stage
   bytes, citing `htlcBip143Preimage_eq_bip143MsgL`,
   `HtlcSpend.successPreimage_eq_bip143MsgL`,
   `HtlcSpend.timeoutPreimage_eq_bip143MsgL`,
   `htlc_preimage_target_summary`, and the two vendor-slice vector theorems.
   Update `PR-02`'s evidence list with the same names plus
   `htlcBip143Preimage_digest_eq_sighashWitnessV0`.
4. **Optional audit registration.** The parent may add the new declaration
   names to `AxiomAudit.lean`; §5 above already audits the representative set.
5. **Gate.** After merging wave-8 lanes, re-run the parent-owned full gate
   (`lake build`, catalog/obligation and anchor scripts, `check-final.py`,
   vendor check, exact `sorry` scan). This lane deliberately did not run them.
6. **No Git write.** The new module and this report remain working-tree files.

## 9. Blockers

- **None remaining in this lane.** Final shared-tree build is `RC 0` (50 jobs).
- Historical blocker only: `LnLean/Protocol/Handshake.lean` was transiently
  broken by another lane (unknown identifiers around its accept-payload edit)
  and its `.olean` was removed, which blocked this module transitively. It was
  not edited here and cleared without intervention. The private-tree build at
  `HEAD` was used as the independent check in the meantime.

## 10. PR-05 / PR-02 recommendation

- **PR-05:** close for the HTLC second-stage preimage bytes. The byte equality
  is unconditional for every `HtlcWire` and every `scriptCode`, and the
  BOLT 3 HTLC-success/timeout scriptCode is synthesized from the faithful
  templates with exact sizes 143/136 and preimage sizes 300/293. Record the
  remaining caveats explicitly: hash images are context, the CLTV push is
  fixed-width, non-anchor HTLC scripts are not synthesized, and the txid is
  supplied in internal order.
- **PR-02:** update the evidence with the HTLC digest theorem and the two
  vector cross-checks. This does not close PR-02 globally (signature
  derivation, key binding and consensus validity remain separate issues), but
  it removes the "HTLC preimage bytes uninstantiated" gap.
- Keep `Seam.htlcBranchScript` out of the `scriptCode` path: the four negative
  theorems document why the faithful templates are required.
