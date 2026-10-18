import LnLean.Bitcoin.Funding
import LnLean.Bitcoin.Laws
import LnLean.Bitcoin.ScriptTemplates
import LnLean.Bitcoin.Seam
import LnLean.Channel.Commitment
import LnLean.Channel.HTLC
import LnLean.Security.Model

/-!
# D03 — The `to_local` commitment output carries the CSV contest delay and
the revocation key.

The catalog target is `LnLean.Bitcoin.toLocalScript`, the seam's structural
`to_local` script template

`<csv> OP_CSV OP_DROP <revocation_pubkey> OP_CHECKSIG`.

The theorems below state the exact byte decomposition of that template and
prove that it contains (a) the length-prefixed push of the CSV contest delay,
(b) the `OP_CSV` and `OP_DROP` opcodes, (c) the length-prefixed push of the
revocation public key, and (d) the final `OP_CHECKSIG`.  They also show that
the script length is `|revocation key| + 6` (39 bytes for a valid 33-byte
compressed key), and that two such scripts determine the same revocation key
bytes and the same encoded delay byte.  Finally, the delay truncation
behaviour of the seam model is recorded: `Blocks` is a `Nat` but
`toLocalScript` encodes it with `Nat.toUInt8`, so only the low byte is
carried.  The conditional recovery theorem restricts to delays below 256.

BOLT anchor: BOLT 3 §"`to_local` Output" (the witness script is
`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
<local_delayedpubkey> OP_ENDIF OP_CHECKSIG`).
LDK anchor: `lightning/src/ln/chan_utils.rs:687`
(`get_revokeable_redeemscript`).

What is *not* modelled: this seam template is the structural
delay-plus-revocation-key fragment, not the full BOLT 3 P2WSH witness script.
In particular the seam places its `revocationPubKey` parameter directly before
`OP_CHECKSIG`; BOLT 3 puts the revocation key in the `OP_IF` penalty branch and
the delayed payment key in the `OP_ELSE` branch.  The delayed-payment branch,
`OP_IF`/`OP_ELSE`, key derivation, SHA256 commitment, script execution, and
spendability are outside this module.  The full witness-script template is
modelled separately in `LnLean.Bitcoin.ScriptTemplates.toLocalWitnessScript`.
-/

namespace LnLean.Proofs.WaveD.D03

set_option autoImplicit false

open LnLean LnLean.Bitcoin

/-! ## Byte containment -/

/-- `hay` contains `needle` as a contiguous byte substring. -/
def waveD_d03_bytesContain (hay needle : ByteArray) : Prop :=
  ∃ pre post : ByteArray, hay = pre ++ needle ++ post

/-- A script contains a byte string. -/
def waveD_d03_scriptContains (s : Script) (needle : ByteArray) : Prop :=
  waveD_d03_bytesContain s.bytes needle

/-- A script contains the minimal push of a public key. -/
def waveD_d03_scriptContainsKey (s : Script) (k : PubKey) : Prop :=
  waveD_d03_scriptContains s (pushData k.bytes)

/-- A script contains a single opcode byte. -/
def waveD_d03_scriptContainsOp (s : Script) (op : UInt8) : Prop :=
  waveD_d03_scriptContains s (ByteArray.empty.push op)

/-- A singleton `ByteArray` has size one. -/
theorem waveD_d03_mk_singleton_size (x : UInt8) : (ByteArray.mk #[x]).size = 1 := rfl

/-- `push` is append of a singleton.  This lets the append lemmas below
normalize the `.push` chains used by the seam builders. -/
theorem waveD_d03_push_eq_append (b : ByteArray) (x : UInt8) :
    b.push x = b ++ ByteArray.empty.push x := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.data_push, ByteArray.data_empty]

/-- Two chained pushes are an append of two singletons. -/
theorem waveD_d03_push_chain_two (a : ByteArray) (x y : UInt8) :
    (a.push x).push y =
      a ++ ByteArray.empty.push x ++ ByteArray.empty.push y := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.data_push, ByteArray.data_empty]

/-! ## Exact shape of the seam `to_local` script -/

/-- The seam `to_local` template is exactly the concatenation of the delay
push, `OP_CSV OP_DROP`, the revocation-key push, and `OP_CHECKSIG`. -/
theorem waveD_d03_toLocalScript_shape (revocationPubKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationPubKey csv).bytes =
      pushData (ByteArray.mk #[csv.toUInt8]) ++
      (ByteArray.empty.push OP_CSV).push OP_DROP ++
      pushData revocationPubKey.bytes ++
      ByteArray.empty.push OP_CHECKSIG := rfl

/-- The same shape written as five separate append components, exposing the
delay push, the two opcodes, the key push, and the final check. -/
theorem waveD_d03_toLocalScript_shape_strong
    (revocationPubKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationPubKey csv).bytes =
      pushData (ByteArray.mk #[csv.toUInt8]) ++
      ByteArray.empty.push OP_CSV ++
      ByteArray.empty.push OP_DROP ++
      pushData revocationPubKey.bytes ++
      ByteArray.empty.push OP_CHECKSIG := by
  rw [waveD_d03_toLocalScript_shape, waveD_d03_push_chain_two]
  simp only [ByteArray.append_assoc, ByteArray.empty_append]

/-! ## The script carries the CSV contest delay -/

/-- The script contains the minimal push of the encoded contest delay. -/
theorem waveD_d03_toLocalScript_carries_delay
    (revocationPubKey : PubKey) (csv : Blocks) :
    waveD_d03_scriptContains (toLocalScript revocationPubKey csv)
      (pushData (ByteArray.mk #[csv.toUInt8])) := by
  refine ⟨ByteArray.empty,
    (ByteArray.empty.push OP_CSV).push OP_DROP ++
      pushData revocationPubKey.bytes ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [waveD_d03_toLocalScript_shape]
  simp only [ByteArray.append_assoc, ByteArray.empty_append]

/-- The script contains the `OP_CSV` opcode that enforces the contest delay. -/
theorem waveD_d03_toLocalScript_carries_csv_opcode
    (revocationPubKey : PubKey) (csv : Blocks) :
    waveD_d03_scriptContainsOp (toLocalScript revocationPubKey csv) OP_CSV := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8]),
    ByteArray.empty.push OP_DROP ++ pushData revocationPubKey.bytes ++
      ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [waveD_d03_toLocalScript_shape, waveD_d03_push_eq_append]
  simp only [ByteArray.append_assoc]

/-- The script contains the `OP_DROP` that removes the delay from the stack
after `OP_CSV` has checked it. -/
theorem waveD_d03_toLocalScript_carries_drop
    (revocationPubKey : PubKey) (csv : Blocks) :
    waveD_d03_scriptContainsOp (toLocalScript revocationPubKey csv) OP_DROP := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8]) ++ ByteArray.empty.push OP_CSV,
    pushData revocationPubKey.bytes ++ ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [waveD_d03_toLocalScript_shape, waveD_d03_push_eq_append]
  simp only [ByteArray.append_assoc]

/-! ## The script carries the revocation key -/

/-- The script contains the minimal push of the revocation public key. -/
theorem waveD_d03_toLocalScript_carries_revocation_key
    (revocationPubKey : PubKey) (csv : Blocks) :
    waveD_d03_scriptContainsKey (toLocalScript revocationPubKey csv) revocationPubKey := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8]) ++
      (ByteArray.empty.push OP_CSV).push OP_DROP,
    ByteArray.empty.push OP_CHECKSIG, ?_⟩
  rw [waveD_d03_toLocalScript_shape]

/-- The script ends with `OP_CHECKSIG`, i.e. the revocation-key push is the
key that controls the output. -/
theorem waveD_d03_toLocalScript_carries_checksig
    (revocationPubKey : PubKey) (csv : Blocks) :
    waveD_d03_scriptContainsOp (toLocalScript revocationPubKey csv) OP_CHECKSIG := by
  refine ⟨pushData (ByteArray.mk #[csv.toUInt8]) ++
      (ByteArray.empty.push OP_CSV).push OP_DROP ++ pushData revocationPubKey.bytes,
    ByteArray.empty, ?_⟩
  rw [waveD_d03_toLocalScript_shape]
  simp only [ByteArray.append_assoc, ByteArray.append_empty]

/-! ## Byte length -/

/-- The seam `to_local` script is six bytes longer than the revocation key:
the one-byte delay push (length + byte), two opcodes, the key's length
prefix, and the final `OP_CHECKSIG`. -/
theorem waveD_d03_toLocalScript_size (revocationPubKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationPubKey csv).bytes.size =
      revocationPubKey.bytes.size + 6 := by
  simp [toLocalScript, pushData, ByteArray.size_append, ByteArray.size_push,
    waveD_d03_mk_singleton_size, ByteArray.size_empty]
  omega

/-- For a valid (33-byte) compressed revocation key the seam `to_local`
script is 39 bytes. -/
theorem waveD_d03_toLocalScript_size_valid
    (revocationPubKey : PubKey) (csv : Blocks)
    (hk : revocationPubKey.Valid) :
    (toLocalScript revocationPubKey csv).bytes.size = 39 := by
  have h := waveD_d03_toLocalScript_size revocationPubKey csv
  unfold PubKey.Valid at hk
  omega

/-! ## The script determines the encoded components -/

/-- Exact byte-list form: delay push, `OP_CSV OP_DROP`, key-length prefix,
key bytes, `OP_CHECKSIG`. -/
theorem waveD_d03_toLocalScript_toList
    (revocationPubKey : PubKey) (csv : Blocks) :
    (toLocalScript revocationPubKey csv).bytes.data.toList =
      [1, csv.toUInt8] ++ [OP_CSV, OP_DROP] ++
      [revocationPubKey.bytes.size.toUInt8] ++
      revocationPubKey.bytes.data.toList ++ [OP_CHECKSIG] := by
  simp [toLocalScript, pushData, ByteArray.data_append, Array.toList_append,
    ByteArray.data_push, waveD_d03_mk_singleton_size, ByteArray.data_empty]

/-- Two seam `to_local` scripts are equal only if they carry the same
revocation-key bytes and the same encoded delay byte.  In particular the
revocation key is not merely present somewhere in the bytes: its length
prefix and position are fixed by the template. -/
theorem waveD_d03_toLocalScript_determines
    (revocationPubKey revocationPubKey' : PubKey) (csv csv' : Blocks)
    (h : toLocalScript revocationPubKey csv =
      toLocalScript revocationPubKey' csv') :
    revocationPubKey.bytes = revocationPubKey'.bytes ∧
      csv.toUInt8 = csv'.toUInt8 := by
  have hsize : revocationPubKey.bytes.size = revocationPubKey'.bytes.size := by
    have hs := congrArg (fun s : Script => s.bytes.size) h
    rw [waveD_d03_toLocalScript_size, waveD_d03_toLocalScript_size] at hs
    omega
  have hlist := congrArg (fun s : Script => s.bytes.data.toList) h
  rw [waveD_d03_toLocalScript_toList, waveD_d03_toLocalScript_toList] at hlist
  have hsplit :
      [1, csv.toUInt8] ++ ([OP_CSV, OP_DROP] ++
        ([revocationPubKey.bytes.size.toUInt8] ++
          (revocationPubKey.bytes.data.toList ++ [OP_CHECKSIG]))) =
      [1, csv'.toUInt8] ++ ([OP_CSV, OP_DROP] ++
        ([revocationPubKey'.bytes.size.toUInt8] ++
          (revocationPubKey'.bytes.data.toList ++ [OP_CHECKSIG]))) := by
    simpa only [List.append_assoc] using hlist
  obtain ⟨hdelayList, hmid⟩ := List.append_inj hsplit (by simp)
  have hdelay : csv.toUInt8 = csv'.toUInt8 := by simpa using hdelayList
  have hmid2 := List.append_cancel_left (as := [OP_CSV, OP_DROP]) hmid
  obtain ⟨hnList, hsuffix⟩ := List.append_inj hmid2 (by simp)
  have _hn : revocationPubKey.bytes.size.toUInt8 =
      revocationPubKey'.bytes.size.toUInt8 := by simpa using hnList
  have hklen : (revocationPubKey.bytes.data.toList).length =
      (revocationPubKey'.bytes.data.toList).length := by
    simp [Array.length_toList, ByteArray.size_data, hsize]
  have hk : revocationPubKey.bytes.data.toList =
      revocationPubKey'.bytes.data.toList :=
    (List.append_inj hsuffix hklen).1
  exact ⟨ByteArray.ext (Array.toList_inj.mp hk), hdelay⟩

/-- `Nat.toUInt8` is injective on values below 256. -/
theorem waveD_d03_toUInt8_injective_of_lt_256 {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h : a.toUInt8 = b.toUInt8) : a = b := by
  have hn := congrArg UInt8.toNat h
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat'] at hn
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hn

/-- For contest delays that fit in one byte (the BOLT 3 script-number range
handled by this seam encoding), the `to_local` script recovers the delay
exactly. -/
theorem waveD_d03_toLocalScript_delay_recoverable
    (revocationPubKey revocationPubKey' : PubKey) (csv csv' : Blocks)
    (h : toLocalScript revocationPubKey csv =
      toLocalScript revocationPubKey' csv')
    (hcsv : csv < 256) (hcsv' : csv' < 256) :
    csv = csv' :=
  waveD_d03_toUInt8_injective_of_lt_256 hcsv hcsv'
    (waveD_d03_toLocalScript_determines revocationPubKey revocationPubKey'
      csv csv' h).2

/-! ## Delays at or above 256 are truncated by the seam encoding -/

/-- The seam template encodes the contest delay as a single byte, so it is
invariant under reduction modulo 256.  This is a faithful statement of what
the current model carries: it does not carry higher bits of `Blocks`. -/
theorem waveD_d03_toLocalScript_delay_mod_256
    (revocationPubKey : PubKey) (csv : Blocks) :
    toLocalScript revocationPubKey csv =
      toLocalScript revocationPubKey (csv % 256) := by
  have hbyte : csv.toUInt8 = (csv % 256).toUInt8 := by
    simp only [Nat.toUInt8_eq]
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_mod]
  unfold toLocalScript
  rw [hbyte]

/-- Mechanized counterexample to full-delay injectivity: delays `0` and
`256` produce the same seam `to_local` script.  Consequently an unconditional
"carries the whole `Blocks` value" claim would be false in this model. -/
theorem waveD_d03_toLocalScript_delay_truncation_counterexample
    (revocationPubKey : PubKey) :
    toLocalScript revocationPubKey 0 = toLocalScript revocationPubKey 256 ∧
      (0 : Blocks) ≠ 256 := by
  constructor
  · have h := waveD_d03_toLocalScript_delay_mod_256 revocationPubKey 256
    simpa using h.symm
  · decide

-- Marker for the catalog obligation.
-- OBLIGATION: LN-WD-D03

end LnLean.Proofs.WaveD.D03
