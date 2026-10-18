# Public `btc-lean` reference and the L1 script seam (L01 audit)

**Audit date:** 2026-10-18
**Auditor:** L01 (public-reference lane), read-only with respect to Lean and
`vendor/`.
**Question:** what is the authoritative public L1 reference, how far is it
from the vendored snapshot, and does its script model close the
funding/`to_local`/HTLC/penalty spendability bridges?

**Short answer.** The authoritative reference is public
`Rob1Ham/btc-lean@4f5c4f8`. The vendored build input is
`vendor/btc-lean-core@f950806`, which is **not in public history**. The public
tree does contain a full script interpreter with `OP_CHECKMULTISIG`,
`OP_CSV`/`OP_CLTV`, P2WSH witness execution, and BIP143 sighashes — but so
does the vendor snapshot; the current LN build imports none of it. The public
`spec/core/Bitcoin/Data/Script.lean` file itself is only the legacy subset
parser and does **not** model those features. No Lean proof in this tree is
proved against the public clone, and that remains the central L1 trust
boundary.

## 1. Repository facts

| Item | Value |
|---|---|
| URL | `https://github.com/Rob1Ham/btc-lean` |
| Branch | `main` |
| Commit | `4f5c4f858fb9ca0743042644453cfa92d30dd271` |
| Commit subject | `btc-lean: Lean 4 model of Bitcoin consensus with row-level Core traceability` |
| Committer date | `2026-10-18T01:29:18Z` |
| Author date | `2026-10-17T22:45:19Z` |
| Tag | `data-2026.10.17` (same commit) |
| Local clone | `/home/ubuntu/btc-lean-public` |
| Read-only symlink | `refs/btc-lean -> /home/ubuntu/btc-lean-public` (untracked) |
| Clone shape | partial clone (`remote.origin.promisor=true`, filter `blob:none`), not shallow |
| History | one release commit (`git rev-list --count HEAD = 1`) |

The public repository is the authoritative L1 reference for review and for
future pin bumps. It is **not** a Lake dependency of this repository.

The vendor snapshot is `vendor/btc-lean-core`, commit
`f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb` (source branch `wallet-peer`;
verified by `vendor/VENDOR-SHA256`, 119 files). Public `main` has no object
for that commit:

```text
$ git -C /home/ubuntu/btc-lean-public cat-file -e f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb
fatal: could not get object info
```

so the public tree is not a fast-forward of the vendor snapshot. The vendor
snapshot remains the build input; the public tree is the reference.

## 2. `spec/core` versus vendor: the 87-path diff

`diff -rq vendor/btc-lean-core /home/ubuntu/btc-lean-public/spec/core` reports
**87 paths**, not 87 modified Lean files:

| Kind | Count | Notes |
|---|---:|---|
| Modified files | 80 | Lean sources, tests, one shell script |
| Only in vendor | 5 | `.lake/` cache, `Test/Script/Parser/__pycache__/`, `Test/Script/Parser/ref.py`, `probe_rc03.lean`, and a self-referential `btc-lean-core` symlink |
| Only in public | 2 | `Bitcoin/Wallet/` (31 `.lean`) and `Test/Wallet/` (2 `.lean`) |

Lean file totals: **114** in the vendor snapshot, **146** in public
`spec/core` (the +32 is the new wallet layer minus `probe_rc03.lean`).

### 2.1 What changed in the 80 modified files

* **36 files** differ only in the Bitcoin Core pin string
  `c50817fe` -> `cce32b168` and the accompanying "Wave N" -> "Review N"
  wording. Example: `Bitcoin/SigHash/Digest.lean:11`
  (`Ground truth @ c50817fe` -> `@ cce32b168`).
* **7 files add declarations/theorems** (the only net line growth):
  * `Bitcoin/TxValidation/Mempool.lean` (+201): TXV-042 mempool coins view
    (`mempoolAddedCoins`, `mempoolAddCoins`, height laws).
  * `Bitcoin/DataLaws/Interface.lean` (+167): TXV-019 Core-faithful weight
    (`serTxWithWitnessCore`, `totalSizeCore`, `txWeightCore`); the old
    `totalSize`/`txWeight` are left untouched.
  * `Bitcoin/Capstone/Block.lean` (+139): BLK-011 `blockMutated` and BLK-021
    weight/commitment ordering; `private def dummyTx` becomes `def dummyTx`.
  * `Bitcoin/Block/Connect.lean` (+120): genesis/connect rules BLK-109/110,
    `hashGenesisBlock`, `isGenesisHeader`, `ConnectState`.
  * `Bitcoin/TxValidation/LocktimeSigOps.lean` (+90): TXV-069 i64 output-sum
    laws (`checkOutputsFoldI64`, no-overflow and agreement theorems).
  * `Bitcoin/Numeric/Amount.lean` (+84): `i64Min`/`i64Max`, `InI64Range`,
    `i64Wrap`, `i64Foldl` range laws.
  * `Bitcoin/Capstone/Merkle.lean` (+41): mutation-cap definitions
    (`levelHasAdjacentDupCap`, `merkleMutationFreeCap`).
* **The other 37 files** contain comment/docstring edits, anchor updates, and
  reworded status notes. No declaration is deleted and no module is removed
  (the only vendor-only Lean file is the debug `probe_rc03.lean`).

### 2.2 The diff that actually matters to this build

`LnLean/Bitcoin/{Seam,Funding,ScriptTemplates,Laws}.lean` import only
`Bitcoin.Data.Basic`, `Bitcoin.Data.Script`, and `Bitcoin.Data.Tx`; their
transitive import closure inside the vendor package is exactly four files:

```text
Bitcoin/RuleAttr.lean
Bitcoin/Data/Basic.lean
Bitcoin/Data/Script.lean
Bitcoin/Data/Tx.lean
```

`Data.Basic`, `Data.Script`, and `Data.Tx` are **byte-identical** between
vendor and public. `RuleAttr.lean` differs by one docstring word
("agents" -> "contributors"). Therefore the 80-file diff changes **nothing**
in the current build's import closure. That is an argument for keeping the
verified vendor snapshot, not for bumping it.

The important semantic/traceability difference is elsewhere: the vendored
`Bitcoin/Interpreter/Defs.lean:15` cites Core `c50817fe`, while public cites
`cce32b168` and the vendored `lakefile.lean` already says `cce32b16`. Public
fixes that internal inconsistency.

## 3. Does the public script model close the LN bridges?

### 3.1 `Bitcoin/Data/Script.lean` alone: no

The file the LN seam imports is the legacy subset parser, identical in both
trees:

* `spec/core/Bitcoin/Data/Script.lean:31-41` — `ScriptInstr` has only
  `push`, `op1negate`, `const`, `nop`, `verify`, `equal`, `equalVerify`,
  `add`, `checkSig`.
* `spec/core/Bitcoin/Data/Script.lean:53-71` — `decodeOp` handles pushes,
  `0x4f`, `0x51-0x60`, `0x61`, `0x69`, `0x87`, `0x88`, `0x93`, `0xac`; every
  other byte returns `none` (line 71).
* `spec/core/Bitcoin/Data/Script.lean:75-85` — `Script.parse` therefore
  returns `none` for any script containing `OP_CHECKMULTISIG` (`0xae`),
  `OP_CLTV` (`0xb1`), `OP_CSV` (`0xb2`), `OP_IF` (`0x63`), etc.

This is exactly why `LnLean/Proofs/PhaseC2/FundingBridge.lean:16-24` makes the
concrete script semantics a structure field and cites
`FundingProps.witnessScript_parse_eq_none_of_wellFormed`
(`LnLean/Proofs/Bitcoin/FundingProps.lean:76`). A bridge built on
`Data.Script.parse` is impossible; that is a proved negative result, not a
gap to paper over.

### 3.2 `spec/core` as a whole: yes, in `Bitcoin/Interpreter`, with caveats

The public tree (and the vendor snapshot) contain a separate, full
interpreter. Concrete evidence:

| Feature | Evidence (public `spec/core`) |
|---|---|
| Full 0x00–0xff parser | `Bitcoin/Script/Parser/Interface.lean:23-27`; AST at `Bitcoin/Script/Parser/Defs.lean:34-44` |
| `OP_CHECKMULTISIG` | dispatch `Bitcoin/Interpreter/Defs.lean:1027-1028`; implementation `:1032-1095`; loop `cmsLoop` `:643-660` |
| `OP_CLTV` | dispatch `:824-832`; semantics `checkLockTimeDef` `:255-263` |
| `OP_CSV` | dispatch `:833-843`; semantics `checkSequenceDef` `:266-282` |
| P2WSH witness execution | `verifyWitnessProgram` `:1211-1231` (32-byte program: last witness item is the script, SHA256 must match, then execute); `executeWitnessScript` `:1167-1200` |
| P2WPKH | `verifyWitnessProgram` `:1223-1229` |
| Top-level per-input check | `verifyScriptFull` `:1305-1310` |
| BIP143 sighash | `Bitcoin/SigHash/Digest.lean:256-336` (`bip143MsgL`, `bip143Digest`) |
| Hashes | `Bitcoin/Interpreter/Hashes.lean:8-14, 125` (`hashSha256`; kernel-decidable implementations) |
| Consensus flags | `Bitcoin/Activation/Interface.lean:75-83`; mainnet selector `Bitcoin/Activation/Flags.lean:147` |

The interpreter header states the scope precisely
(`Bitcoin/Interpreter/Defs.lean:47-52`): P2WSH/P2WPKH are fully judged;
Taproot **script-path** spending stops at `VerifyTaprootCommitment` and
returns `VerifyOutcome.unjudged`. LN commitment outputs are v0 P2WSH, so that
limitation does not block the LN bridges.

What is deliberately abstracted:

* ECDSA/Schnorr verification is a `ScriptChecker` parameter
  (`Bitcoin/Interpreter/Interface.lean:31-44`, IC-2), assembled from
  `Bitcoin/Crypto/Seam/Entry.lean`; the BIP143 digest is available but the
  LN side must instantiate the checker with the spent output's amount and
  scriptCode.
* The interpreter is a model of Core, not a proved-equivalent extract of
  `bitcoind`; the public `docs/TCB.md:1-40` says so explicitly, and
  `docs/RESIDUALS.md` lists 26 proved rows whose Lean target does not entail
  the full row claim.
* The legacy `Bitcoin/Script/Interp.lean` is a **different, toy** subset
  interpreter (`:1-20`: stub `OP_CHECKSIG`, no branches/P2SH). It must not be
  confused with `Bitcoin.Interpreter.Defs`.

**Verdict for the bridges.** The opcode and witness machinery needed by the
BOLT 3 funding (`2 <pk1> <pk2> 2 OP_CHECKMULTISIG`), `to_local`
(revocation/CSV branches), offered/received HTLC (hash/CLTV branches), and
penalty (revocation path) scripts is present and executable in
`Bitcoin.Interpreter.Defs`. Spendability is still **not proved** in this
repository: the current proofs take the L1 acceptance predicate as a
structure field (`FundingSpendBridge.verify`, `HTLCSpendBridge`,
`PenaltyL1Bridge.accepted`/`spends`). Closing that requires a new bridge
module that imports the interpreter and instantiates `ScriptChecker`,
`sighashDispatch`, and the mainnet flags — not a vendor bump.

### 3.3 Is there a better concrete seam to use later?

Not in public versus vendor: public adds no new interpreter entry point. The
useful seam already exists in the vendored snapshot with the same API:

```text
vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean:1027  checkMultiSig
vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean:1167  executeWitnessScript
vendor/btc-lean-core/Bitcoin/Interpreter/Defs.lean:1211  verifyWitnessProgram
vendor/btc-lean-core/Bitcoin/Script/Parser/Defs.lean      full parser
vendor/btc-lean-core/Bitcoin/SigHash/Digest.lean:256      BIP143
```

Those files differ from public only in pin comments/wording (equal line
counts), so a later bridge can import them from the vendor today. The
recommended next smallest step is an additive
`LnLean/Bitcoin/InterpreterBridge.lean` that imports
`Bitcoin.Interpreter.Defs`, `Bitcoin.Script.Parser.Interface`, and
`Bitcoin.SigHash.Digest`, and proves one concrete theorem
(`verifyScriptFull` on the BOLT 3 funding witness reduces to the two
signature checks), with the checker and sighash as explicit hypotheses. That
is a new proof lane, not part of L01.

## 4. Can the vendor be bumped safely now?

**No, not in this repair.** The facts:

* `f950806` is absent from public history; the bump replaces a digest-verified
  snapshot with a separate lineage, so it is not a fast-forward.
* 80 files differ, 7 of them add declarations; 33 public files have no vendor
  counterpart (wallet layer). A full rebuild is mandatory.
* `vendor/VENDOR-SHA256` (119 files) would have to be regenerated, and the
  four in-tree vendor citations
  (`FundingBridge.lean:17,21`, `WaveD/D36.lean:47`,
  `Bitcoin/FundingProps.lean:76`) would need a line-anchor review. Only
  `scripts/verify-anchors.py` checks rust-lightning anchors; vendor anchors
  are review-only.
* The current import closure is unaffected (`Data.*` identical), so there is
  no build-driven reason to bump now.
* The public clone is a single squashed release commit; there is no
  commit-by-commit provenance for the changes.

If a bump is wanted later, treat it as its own lane: pick the public commit,
copy `spec/core`, regenerate the manifest, run a full clean
`lake build` at RC 0, then `verify-anchors.py` and `check.sh`, and record the
new URL/commit/date in `refs/PINNED.md` and `docs/L1-PIN.md`.

## 5. Remaining L1 trust boundary (exact)

1. The build imports only the four vendor modules listed in §2.2. It does not
   import `Bitcoin.Interpreter`, `Bitcoin.Script.Parser`, `Bitcoin.SigHash`,
   or `Bitcoin.TxValidation`.
2. No LN theorem proves script execution, witness acceptance, or
   spendability. The Phase-C2 bridges are conditional on structure fields
   (`FundingSpendBridge`, `HTLCSpendBridge`, `PenaltyL1Bridge`); see
   `LnLean/Proofs/PhaseC2/{FundingBridge,HTLCBridge,PenaltyBridge}.lean`.
3. The public `spec/core` is not imported into this build, and no proof in
   this tree is checked against it.
4. Even after importing the interpreter, the remaining obligations are: the
   signature checker and BIP143 sighash instantiation, the consensus flag
   word, the SHA-256 witness-program hash bridge, and a statement-fidelity
   review against Core. Taproot script-path spends stay `unjudged`.
5. The vendor snapshot itself is trusted as the L1 model (`f950806`,
   digest-verified). Its interpreter cites Core `c50817fe`, whereas public
   cites `cce32b168`; that pin discrepancy is a traceability caveat for the
   eventual bump.

## 6. Evidence commands

```sh
cd /home/ubuntu/ln-lean-repair

# public identity
git -C /home/ubuntu/btc-lean-public remote get-url origin
git -C /home/ubuntu/btc-lean-public rev-parse HEAD
git -C /home/ubuntu/btc-lean-public log -1 --format='%H%n%ci%n%s'
git -C /home/ubuntu/btc-lean-public cat-file -e f95080638ae571a3664f4f41b9b6f6b4cfa7c5eb  # must fail

# diff
diff -rq vendor/btc-lean-core /home/ubuntu/btc-lean-public/spec/core | wc -l   # 87
diff -rq vendor/btc-lean-core /home/ubuntu/btc-lean-public/spec/core | grep -c '^Files '  # 80

# byte identity of the imported closure
for f in Bitcoin/Data/Basic.lean Bitcoin/Data/Script.lean Bitcoin/Data/Tx.lean; do
  diff -q "vendor/btc-lean-core/$f" "/home/ubuntu/btc-lean-public/spec/core/$f"
done

# script features
grep -n '0xae\|0xb1\|0xb2' /home/ubuntu/btc-lean-public/spec/core/Bitcoin/Interpreter/Defs.lean
grep -n 'def verifyWitnessProgram\|def executeWitnessScript\|def verifyScriptFull' \
  /home/ubuntu/btc-lean-public/spec/core/Bitcoin/Interpreter/Defs.lean

# integrity
./scripts/check-public-reference.sh
./scripts/verify-vendor.sh
```

## 7. Reproduce the verdict

`./scripts/check-public-reference.sh` checks the clone URL, `HEAD`, local
commit object, tag, and that `lakefile.lean` does not depend on the clone; it
then runs `scripts/verify-vendor.sh`. It is offline by default and does not
modify `vendor/` or the clone.
