# S7-PR-PREIMAGE — exact BIP 143 preimage byte equality with the vendored encoder

**Lane:** `S7-PR-PREIMAGE` (`PR-05`, `PR-02`).
**Branch:** `repair/integrated`, wave-7 launch `3180581`.
**Worktree:** `/home/ubuntu/ln-lean-repair`.
**Verdict:** **target met for the modelled fields.** `Bip143Preimage.preimageBytes`
is proved byte-equal to the vendored `Bitcoin.SigHash.bip143MsgL` (list level) and
to `LnLean.Bitcoin.Sighash.encode` (literal `ByteArray` equality), including the
wire outpoint, scriptCode CompactSize prefix, and the internal byte order of all
hash fields. The only remaining condition for an *arbitrary* preimage (as opposed
to a transaction-derived one) is the explicit field-agreement context; that
context is stated as a general theorem, so no context item is hidden.

- Owned files touched:
  - `LnLean/Proofs/Channel/SighashTargets.lean` — additive `import
    LnLean.Bitcoin.Sighash` (line 87) and new §13 (line 1451), **+334 / −0**.
  - `LnLean/Bitcoin/Sighash.lean` — additive general refinement theorem,
    **+29 / −0**.
  - `agents/reports/swarm7/S7-PR-PREIMAGE.md` — this report.
- Not modified: `Messages.lean`, `Commitment.lean`, `State.lean`, `LnLean.lean`,
  `Obligations.lean`, `Traceability.lean`, `AxiomAudit.lean`,
  `scripts/check-final.py`, shared docs, other lanes' files, vendor sources.
- No Git write was performed.
- No `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` /
  `@[implemented_by]` was introduced (scan in §6).

## 1. Result in one paragraph

§12 left two serializers: the exact-wire `Bip143Preimage.preimageBytes` and the
vendored `bip143MsgL`. §13 closes the gap. `Bip143Preimage.toPreimage` bridges the
wire record to `LnLean.Bitcoin.Sighash.Preimage`; the serializer
`preimageBytes` is proved byte-equal to `Sighash.encode` for **every**
`Bip143Preimage`, and to the vendored `bip143MsgL` for every preimage derived by
`Bip143Preimage.ofTx` (including `CommitmentWire.toTx`). A general theorem
`Sighash.bL_encode_eq_bip143MsgL` states the exact refinement for an arbitrary
model `Preimage`: equality holds under eight explicit field-agreement
hypotheses, which are exactly the missing transaction context. Three new
`decide`-checked vectors pin the bytes of a commitment-wire preimage (179 bytes),
its outpoint slice, its scriptCode prefix, and the three-byte CompactSize path for
a 253-byte scriptCode (412 bytes), and cross-check the same bytes against the
vendored encoder.

## 2. Files changed

| File | Change |
|---|---|
| `LnLean/Bitcoin/Sighash.lean` | Added `bL_encode_eq_bip143MsgL` after `bL_encode_ofTx` (line 456): the strongest exact refinement for an arbitrary `Preimage` under explicit field-agreement hypotheses. |
| `LnLean/Proofs/Channel/SighashTargets.lean` | Added `import LnLean.Bitcoin.Sighash` (line 87) and §13 (line 1451): bridge record/function, field serializer lemmas, transaction/wire derivation, digest equality, and byte-level vectors. |
| `agents/reports/swarm7/S7-PR-PREIMAGE.md` | This report. |

The diff is `+334 / −0` in `SighashTargets.lean` and `+29 / −0` in
`Sighash.lean`. Every pre-existing §12 declaration (`CommitmentWire`,
`HtlcWire`, `Bip143Preimage.preimageBytes`, parser round-trips, size theorems,
125/158-byte vectors, `viewOfWire`/`SharedEq`, and
`structuralView_not_determine_scripts`) is untouched and still builds.

## 3. Exact signatures

All new names are in `namespace LnLean.Proofs.Channel.SighashTargets` unless
prefixed `LnLean.Bitcoin.Sighash`. `bL` is
`Bitcoin.Serialization.bL : ByteArray → List UInt8`.

### 3.1 In `LnLean/Bitcoin/Sighash.lean`

```lean
theorem bL_encode_eq_bip143MsgL (p : Preimage) (tx : Tx) (nIn : Nat)
    (amount : Amount)
    (hversion : p.version = tx.version.toUInt32)
    (hprev : bL p.hashPrevouts = Bitcoin.SigHash.hashPrevoutsL tx p.hashType)
    (hseq : bL p.hashSequence = Bitcoin.SigHash.hashSequenceL tx p.hashType)
    (houtpoint : p.outpoint = (tx.vin.getD nIn dummyTxIn).prevout)
    (hseq2 : p.sequence = (tx.vin.getD nIn dummyTxIn).sequence)
    (hout : bL p.hashOutputs = Bitcoin.SigHash.hashOutputsL tx nIn p.hashType)
    (hlock : p.lockTime = tx.locktime)
    (hamount : p.amount = amount) :
    bL (encode p) =
      Bitcoin.SigHash.bip143MsgL tx nIn (bL p.scriptCode) p.hashType amount
```

The hypotheses are complete: version, the three sub-hashes (at the vendored
list level where they are computed), outpoint, input sequence, locktime, and
amount. Nothing else is needed for literal equality.

### 3.2 Bridge record and serializer agreement (§13.1–13.2)

```lean
def Bip143Preimage.toPreimage (p : Bip143Preimage) :
    LnLean.Bitcoin.Sighash.Preimage
-- version/hashPrevouts/hashSequence/scriptCode/sequence/hashOutputs/lockTime/
-- hashType copied verbatim; outpoint := ⟨p.outpointTxid, p.outpointIndex⟩;
-- amount := (p.amountSat.toNat : Int).

theorem bL_exactU32 (x : UInt32) :
    bL (exactU32 x) = Bitcoin.SigHash.serU32L x

theorem bL_exactU64 (x : UInt64) :
    bL (exactU64 x) = Bitcoin.SigHash.serU64L x

theorem bL_exactCS (n : Nat) :
    bL (exactCS n) = Bitcoin.Serialization.encCSL n

theorem serU64L_ofNat_toNat (x : UInt64) :
    Bitcoin.SigHash.serU64L (UInt64.ofInt (Int.ofNat x.toNat)) =
      Bitcoin.SigHash.serU64L x

theorem Bip143Preimage.preimageBytes_fields (p : Bip143Preimage) :
    bL p.preimageBytes =
      Bitcoin.SigHash.serU32L p.version ++ bL p.hashPrevouts ++
      bL p.hashSequence ++ bL p.outpointTxid ++
      Bitcoin.SigHash.serU32L p.outpointIndex ++
      Bitcoin.Serialization.encCSL p.scriptCode.size ++ bL p.scriptCode ++
      Bitcoin.SigHash.serU64L p.amountSat ++
      Bitcoin.SigHash.serU32L p.sequence ++ bL p.hashOutputs ++
      Bitcoin.SigHash.serU32L p.locktime ++
      Bitcoin.SigHash.serU32L p.sighashType

theorem Bip143Preimage.preimageBytes_eq_encode (p : Bip143Preimage) :
    bL p.preimageBytes = bL (LnLean.Bitcoin.Sighash.encode p.toPreimage)

theorem Bip143Preimage.preimageBytes_eq_encode_bytes (p : Bip143Preimage) :
    p.preimageBytes = LnLean.Bitcoin.Sighash.encode p.toPreimage
```

`preimageBytes_fields` is the explicit byte-order statement: the txid is the
32-byte internal-order value, the index is 4-byte LE, the scriptCode is
CompactSize-prefixed, and the three hash fields are inserted verbatim (no
reversal). `preimageBytes_eq_encode_bytes` is a genuine `ByteArray` equality,
not only a list equality.

### 3.3 Transaction/wire derivation and vendor equality (§13.3)

```lean
def Bip143Preimage.ofTx (tx : Bitcoin.Data.Tx) (nIn : Nat)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    Bip143Preimage
-- version := tx.version.toUInt32
-- hashPrevouts/hashSequence/hashOutputs := Sighash.hash*Of tx …
-- outpointTxid/outpointIndex/sequence := (tx.vin.getD nIn dummyTxIn)…
-- amountSat := amountSat, locktime := tx.locktime, sighashType := ht

theorem Bip143Preimage.toPreimage_ofTx (tx …) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).toPreimage =
      LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht (amountSat.toNat : Int)

theorem Bip143Preimage.ofTx_hashPrevouts (tx …) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashPrevouts =
      Bitcoin.SigHash.hashPrevoutsL tx ht

theorem Bip143Preimage.ofTx_hashSequence (tx …) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashSequence =
      Bitcoin.SigHash.hashSequenceL tx ht

theorem Bip143Preimage.ofTx_hashOutputs (tx …) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).hashOutputs =
      Bitcoin.SigHash.hashOutputsL tx nIn ht

theorem Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) :
    bL (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL tx nIn (bL scriptCode) ht
        (amountSat.toNat : Int)

theorem Bip143Preimage.preimageBytes_eq_encode_ofTx (tx …) :
    (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).preimageBytes =
      LnLean.Bitcoin.Sighash.encode
        (LnLean.Bitcoin.Sighash.ofTx tx nIn scriptCode ht
          (amountSat.toNat : Int))

def commitmentBip143Preimage (w : CommitmentWire) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) : Bip143Preimage :=
  Bip143Preimage.ofTx w.toTx 0 scriptCode ht amountSat

theorem commitmentBip143Preimage_wire_fields (w : CommitmentWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    (commitmentBip143Preimage w scriptCode ht amountSat).version = w.version ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointTxid =
      w.fundingTxid ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).outpointIndex =
      w.fundingOutputIndex ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).sequence = w.sequence ∧
    (commitmentBip143Preimage w scriptCode ht amountSat).locktime = w.locktime

theorem commitmentBip143Preimage_eq_bip143MsgL (w : CommitmentWire)
    (scriptCode : ByteArray) (ht : UInt32) (amountSat : UInt64) :
    bL (commitmentBip143Preimage w scriptCode ht amountSat).preimageBytes =
      Bitcoin.SigHash.bip143MsgL w.toTx 0 (bL scriptCode) ht
        (amountSat.toNat : Int)
```

The last theorem is the direct §12→§13 tie: the exact `CommitmentWire`
transaction from §12 is the transaction argument of the vendored BIP 143
encoder, and its funding outpoint/sequence/locktime are the preimage fields.
The sub-hashes are the vendored `hash*L` folds over that same wire transaction
(not independent inputs).

### 3.4 Digest equality (§13.4)

```lean
theorem dshaL_bL_eq_dsha (b : ByteArray) :
    Bitcoin.SigHash.dshaL (bL b) = LnLean.Bitcoin.Sighash.dsha b

theorem Bip143Preimage.toPreimage_digest_eq_dshaL (p : Bip143Preimage) :
    LnLean.Bitcoin.Sighash.digest p.toPreimage =
      Bitcoin.SigHash.dshaL (bL p.preimageBytes)

theorem Bip143Preimage.digest_eq_sighashWitnessV0_ofTx
    (tx : Bitcoin.Data.Tx) (nIn : Nat) (scriptCode : ByteArray)
    (ht : UInt32) (amountSat : UInt64) (h : nIn < tx.vin.length) :
    LnLean.Bitcoin.Sighash.digest
        (Bip143Preimage.ofTx tx nIn scriptCode ht amountSat).toPreimage =
      Bitcoin.SigHash.signatureHashBip143Impl tx nIn (bL scriptCode) ht
        (amountSat.toNat : Int)

theorem exactSighashDigest_eq_vendor_of_model
    (M : LnLean.Crypto.PrimitiveModel)
    (hM : ∀ b, M.sha256 b = Bitcoin.Crypto.Seam.sha256 b)
    (p : Bip143Preimage) :
    exactSighashDigest M p = Bitcoin.SigHash.dshaL (bL p.preimageBytes)

theorem exactSighashDigest_eq_digest_of_model
    (M : LnLean.Crypto.PrimitiveModel)
    (hM : ∀ b, M.sha256 b = Bitcoin.Crypto.Seam.sha256 b)
    (p : Bip143Preimage) :
    exactSighashDigest M p = LnLean.Bitcoin.Sighash.digest p.toPreimage
```

`dshaL` is the vendored hash floor (`Bitcoin.Crypto.Seam.sha256d`), so the
digest is over exactly the bytes whose equality is proved above. The
`PrimitiveModel` identification is explicit (`hM`), not assumed.

### 3.5 Byte-level vectors (§13.5)

```lean
def vectorWirePreimage : Bip143Preimage :=
  commitmentBip143Preimage vectorWire vectorMeta.fundingScript 0x82 3000

theorem vectorWirePreimage_bytes :
    bL vectorWirePreimage.preimageBytes =
      [0x02,0x00,0x00,0x00] ++ List.replicate 32 0x00 ++
      List.replicate 32 0x00 ++ List.replicate 32 0x11 ++
      [0x00,0x00,0x00,0x00, 0x16,0x00,0x14] ++
      List.replicate 20 0x44 ++
      [0xb8,0x0b,0x00,0x00,0x00,0x00,0x00,0x00,
       0x00,0x00,0x00,0x80] ++
      List.replicate 32 0x00 ++
      [0x00,0x00,0x00,0x20, 0x82,0x00,0x00,0x00]

theorem vectorWirePreimage_size :
    (bL vectorWirePreimage.preimageBytes).length = 179

theorem vectorWirePreimage_vendor_bytes :
    Bitcoin.SigHash.bip143MsgL vectorWire.toTx 0
        (bL vectorMeta.fundingScript) 0x82 3000 =
      <the same 179-byte list>
```

Both sides are `decide`-checked independently, and
`vectorWirePreimage_vendor` derives the same equality from
`commitmentBip143Preimage_eq_bip143MsgL`. Extra slices:

```lean
theorem vectorWirePreimage_outpoint_bytes :
    ((bL vectorWirePreimage.preimageBytes).drop 68).take 36 =
      List.replicate 32 0x11 ++ [0x00,0x00,0x00,0x00]

theorem vectorWirePreimage_scriptCode_bytes :
    ((bL vectorWirePreimage.preimageBytes).drop 104).take 3 =
      [0x16, 0x00, 0x14]

def vectorLongScript : ByteArray := byteList (List.replicate 253 0x77)
def vectorLongPreimage : Bip143Preimage :=
  commitmentBip143Preimage vectorWire vectorLongScript 0x82 3000

theorem vectorLongPreimage_size :
    (bL vectorLongPreimage.preimageBytes).length = 412

theorem vectorLongPreimage_scriptCode_prefix :
    ((bL vectorLongPreimage.preimageBytes).drop 104).take 3 =
      [0xfd, 0xfd, 0x00]

theorem vectorLongPreimage_vendor_prefix :
    ((Bitcoin.SigHash.bip143MsgL vectorWire.toTx 0
        (bL vectorLongScript) 0x82 3000).drop 104).take 3 =
      [0xfd, 0xfd, 0x00]

theorem vectorPreimage_encode_bytes :
    bL (LnLean.Bitcoin.Sighash.encode vectorPreimage.toPreimage) =
      <the existing 158-byte §12 vector>
```

The vectors use `SIGHASH_NONE|ANYONECANPAY` (`0x82`) deliberately: the three
sub-hashes are then the BIP 143 zero vector, so the kernel `decide` checks the
vendored encoder's field order and byte order without evaluating SHA-256. The
non-zero sub-hash path is covered symbolically by
`bL_encode_ofTx` / `bL_hash*Of` (already in `Sighash.lean`), which are
byte-equality theorems, not `decide` tests.

## 4. Build result

Shared tree at `3180581` with the concurrent wave-7 lane edits present:

```bash
cd /home/ubuntu/ln-lean-repair
LEAN_NUM_THREADS=1 flock -w 1800 /tmp/opencode/btc-lean/build.lock \
  lake build LnLean.Bitcoin.Sighash LnLean.Proofs.Channel.SighashTargets
```

Result:

```text
✔ [21/30] Built LnLean.Bitcoin.Sighash
…
✔ [47/47] Built LnLean.Proofs.Channel.SighashTargets (2.6s)
Build completed successfully (47 jobs).  RC 0
```

Transient note: an earlier run failed in `LnLean/Protocol/Handshake.lean`
(concurrent `S7-L1-FUNDING-AUTH` edit, lines 702/712/729/748) before reaching
this lane. The final run above was taken after that lane settled; no change to
another lane's file was made. A private validation copy with
`Handshake/Commitment/State` at `HEAD` also built `[47/47]`, so the §13 proof
does not depend on the concurrent edits.

## 5. Axiom audit

Run in the shared tree with
`lake env lean /tmp/opencode/AxiomsPreimage.lean` (scratch file, not in the
repository). Representative output:

```text
LnLean.Bitcoin.Sighash.bL_encode_eq_bip143MsgL        [propext, Classical.choice, Quot.sound]
Bip143Preimage.preimageBytes_fields                   [propext, Quot.sound]
Bip143Preimage.preimageBytes_eq_encode                [propext, Quot.sound]
Bip143Preimage.preimageBytes_eq_encode_bytes          [propext, Quot.sound]
Bip143Preimage.toPreimage_ofTx                        [propext, Classical.choice, Quot.sound]
Bip143Preimage.ofTx_hashPrevouts                      [propext, Classical.choice, Quot.sound]
Bip143Preimage.ofTx_hashSequence                      [propext, Classical.choice, Quot.sound]
Bip143Preimage.ofTx_hashOutputs                       [propext, Classical.choice, Quot.sound]
Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx       [propext, Classical.choice, Quot.sound]
Bip143Preimage.preimageBytes_eq_encode_ofTx           [propext, Classical.choice, Quot.sound]
commitmentBip143Preimage_wire_fields                  [propext, Classical.choice, Quot.sound]
commitmentBip143Preimage_eq_bip143MsgL                [propext, Classical.choice, Quot.sound]
dshaL_bL_eq_dsha                                      [propext, Quot.sound]
Bip143Preimage.toPreimage_digest_eq_dshaL             [propext, Quot.sound]
Bip143Preimage.digest_eq_sighashWitnessV0_ofTx        [propext, Classical.choice, Quot.sound]
exactSighashDigest_eq_vendor_of_model                 [propext, Quot.sound]
exactSighashDigest_eq_digest_of_model                 [propext, Quot.sound]
bL_exactU32                                           [propext]
bL_exactU64                                           [propext]
bL_exactCS                                            [propext, Quot.sound]
serU64L_ofNat_toNat                                   [propext]
vectorWirePreimage_bytes                              [propext, Classical.choice, Quot.sound]
vectorWirePreimage_size                               [propext, Classical.choice, Quot.sound]
vectorWirePreimage_vendor_bytes                       [propext, Classical.choice, Quot.sound]
vectorWirePreimage_vendor                             [propext, Classical.choice, Quot.sound]
vectorWirePreimage_outpoint_bytes                     [propext, Classical.choice, Quot.sound]
vectorWirePreimage_scriptCode_bytes                   [propext, Classical.choice, Quot.sound]
vectorLongPreimage_size                               [propext, Classical.choice, Quot.sound]
vectorLongPreimage_scriptCode_prefix                  [propext, Classical.choice, Quot.sound]
vectorLongPreimage_vendor_prefix                      [propext, Classical.choice, Quot.sound]
vectorPreimage_encode_bytes                           [propext, Quot.sound]
```

Union: exactly `{propext, Quot.sound, Classical.choice}`. No unlisted axiom.

## 6. Forbidden-construct scan

```bash
grep -nE '\b(sorry|admit|native_decide|unsafe)\b|@\[implemented_by\]|^axiom |\baxiom [A-Za-z]' \
  LnLean/Proofs/Channel/SighashTargets.lean LnLean/Bitcoin/Sighash.lean
```

Result: no matches (exit 1). `decide` is used only on closed concrete vectors
(and two existing §12 closed cases); the kernel still checks the resulting proof
term, so this is ordinary `decide`, not `native_decide`.

## 7. Scope caveats and the exact missing context

1. **Arbitrary preimage vs. transaction-derived preimage.** For every
   `Bip143Preimage` we prove literal `ByteArray` equality to the model encoder
   `Sighash.encode` and the full ten-field byte expansion. Literal equality to
   the vendored `bip143MsgL` also needs a transaction `tx` and index `nIn` whose
   derived version, three sub-hashes, outpoint, sequence, locktime and amount
   are the preimage fields. Those are exactly the eight hypotheses of
   `Sighash.bL_encode_eq_bip143MsgL`; `Bip143Preimage.ofTx` discharges all of
   them by construction. No other field is missing.
2. **Byte order.** Txids and the three sub-hashes are the consensus-internal
   32-byte values, inserted verbatim. No display-order reversal, RPC hex
   conversion, or `GetHex` theorem is modelled; the vendored encoder inserts
   the same lists, so the two agree by the field theorem and
   `ofTx_hash*`/`commitmentBip143Preimage_wire_fields`.
3. **`scriptCode`.** Supplied as opaque bytes and CompactSize-prefixed. No
   P2WPKH/P2WSH scriptCode reconstruction, `OP_CODESEPARATOR`, or
   `FindAndDelete` behaviour is modelled. The vector exercises both the 1-byte
   (`0x16`) and 3-byte (`0xfd 0xfd 0x00`) CompactSize paths.
4. **Amount.** `Bip143Preimage.amountSat : UInt64` is lifted to the signed
   `Amount` via `toNat`. `serU64L_ofNat_toNat` proves the serializer agreement
   for every 64-bit value, including values ≥ 2^63. Core's `amount ≥ 0`
   witness-v0 precondition and negative `CAmount` values are outside the
   `UInt64` model; `Sighash.lean` documents the signed `Amount` serialization
   separately.
5. **Sub-hash derivation for non-ACP types.** The concrete `decide` vector uses
   `0x82` so the sub-hashes are the zero vector; non-zero sub-hashes are proved
   equal to the vendored fold at the list level (`bL_hashPrevoutsOf`,
   `bL_hashSequenceOf`, `bL_hashOutputsOf`), not recomputed by `decide`. No
   SHA-256 injectivity or collision resistance is used.
6. **Digest.** `Sighash.digest` uses the vendor seam `sha256d`; the abstract
   `PrimitiveModel` digest agrees only under the explicit
   `M.sha256 = Seam.sha256` hypothesis (`exactSighashDigest_eq_vendor_of_model`).
   No computational claim is made.
7. **No consensus claim.** Nothing here proves script/signature validity,
   transaction validity, mempool policy, or node acceptance. The existing §12
   scope notes (witness `[[]]`, output ordering, obscurer derivation, fees,
   HTLC-side bridge, parser domain) are unchanged and still apply.
8. **HTLC second stage.** The wire bridge is instantiated for
   `CommitmentWire`; `HtlcWire` still has its §12 layout/parser result only.
   The same `Bip143Preimage.ofTx` construction applies to `HtlcWire.toTx`, but
   this lane did not add that instantiation; it is a mechanical follow-up, not a
   missing context field.

## 8. Integration steps for the parent

1. Keep the additive `import LnLean.Bitcoin.Sighash` at
   `SighashTargets.lean:87`; no root import or `LnLean.lean` change is needed
   (the module is already in the import graph).
2. No catalog row is required for compilation. To record the evidence, update
   `PR-05` to **closed (exact for transaction-derived preimages)** citing:
   `Bip143Preimage.preimageBytes_eq_bip143MsgL_ofTx`,
   `commitmentBip143Preimage_eq_bip143MsgL`,
   `Bip143Preimage.preimageBytes_eq_encode_bytes`,
   `Sighash.bL_encode_eq_bip143MsgL`, and the vector theorems. Update `PR-02`'s
   evidence with the same names. The `PR-05` "next action" should keep the
   scriptCode-synthesis gap and the arbitrary-preimage context caveat.
3. Optionally add the new declaration names to `AxiomAudit.lean` (parent-owned);
   the audit output in §5 already covers them.
4. Re-run the full gate (`lake build`, strict catalog audit, `check.sh`,
   `check-final.py`, `check-conformance.py`, `verify-anchors.py`,
   `verify-vendor.sh`, exact `sorry` scan) after merging the wave-7 lanes.
5. No Git write was performed by this lane; the changes are working-tree
   modifications only.

## 9. Blockers

- **None in this lane.** The shared-tree build is `RC 0` (47 jobs) after the
  concurrent `Handshake.lean` edit settled.
- Operational note only: during the lane, `LnLean/Protocol/Handshake.lean` was
  transiently broken by another lane, which blocked this module transitively
  (it imports `Messages`/`Commitment`/`ProtocolSigningTargets`). It was not
  edited here and cleared on its own.
- No `git` operation, no full build, no `collect-*` script was run.

## 10. Summary for the parent

- `Bip143Preimage.preimageBytes` is now proved byte-equal to the vendored
  `Bitcoin.SigHash.bip143MsgL` for every transaction-derived preimage, and to
  `LnLean.Bitcoin.Sighash.encode` for every `Bip143Preimage`, including the
  `CommitmentWire` instance from §12. Script/outpoint bytes, the CompactSize
  scriptCode prefix, and the internal order of all hash fields are explicit.
- The strongest general refinement is `Sighash.bL_encode_eq_bip143MsgL`: literal
  vendored equality for an arbitrary model `Preimage` under eight precise
  field-agreement hypotheses (the complete missing transaction context).
- Digest equality follows: `digest p.toPreimage = dshaL (bL p.preimageBytes)`
  and, for in-range inputs, `= signatureHashBip143Impl`; the abstract
  `PrimitiveModel` version is conditional on `M.sha256 = Seam.sha256`.
- New `decide` vectors: a 179-byte commitment-wire `SIGHASH_NONE|ANYONECANPAY`
  preimage matching the vendored encoder byte-for-byte (with outpoint/scriptCode
  slices), a 412-byte 253-byte-scriptCode vector proving the `0xfd` CompactSize
  path, and the existing 158-byte §12 vector checked through `Sighash.encode`.
- Build: `[47/47]`, RC 0, shared tree at `3180581`. Axioms: only
  `{propext, Quot.sound, Classical.choice}`. Forbidden-token scan: empty.
- Caveats kept: txid/sub-hash display-order conversion, scriptCode synthesis,
  signed/negative amounts, non-ACP concrete hashing, HTLC-side instantiation,
  and all §12 consensus-boundary notes.
