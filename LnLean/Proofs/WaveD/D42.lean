import LnLean.Bitcoin.ScriptTemplates
import LnLean.Channel.Commitment
import LnLean.Channel.Types
import LnLean.Proofs.Bitcoin.ScriptProps

/-!
# LnLean.Proofs.WaveD.D42 — the `to_local` script commits to the CSV delay

English claim (catalog `LN-L1-004`).  The `to_local` commitment output script
commits to the CSV contest delay (`to_self_delay`), including the exact
opcode/value representation used by the model.

The model builds the `to_local` witness script as

`OP_IF <revocationpubkey> OP_ELSE <to_self_delay> OP_CSV OP_DROP
 <local_delayedpubkey> OP_ENDIF OP_CHECKSIG`

(`LnLean.Bitcoin.ScriptTemplates.toLocalWitnessScript`), where
`<to_self_delay>` is `pushScriptNum16 toSelfDelay = pushData (pushUInt16LE d)`
— the scaffold's *fixed-width* two-byte little-endian script-number push, i.e.
the three bytes `[0x02, d % 256, (d / 256) % 256]`.  The on-chain output is
the P2WSH `toLocalScriptPubKey hash = p2wsh hash`, and
`CommitmentParams.HashesMatch` names the (unproved) bridge saying `hash` is
`SHA256` of that witness script.

This module proves, at the level of raw `Script.bytes`:

* the exact decomposition of the script around the delay push
  (`waveD_d42_toLocal_decomp`), so the delay push is a contiguous substring
  between the two key pushes;
* the exact byte layout of the delay push: length byte `0x02`, low byte then
  high byte little-endian (`waveD_d42_pushScriptNum16_data_toList`,
  `waveD_d42_toLocal_delay_encoding`), followed immediately by `OP_CSV`
  (`0xb2`) and `OP_DROP` (`0x75`) at fixed offsets 39/40 once the revocation
  key is a 33-byte compressed key (`waveD_d42_toLocal_csvOpcode`,
  `waveD_d42_toLocal_dropOpcode`);
* the delay value is recoverable from the script bytes at offsets 37/38
  (`waveD_d42_toLocal_delayBytes_toNat`,
  `waveD_d42_contestDelay_delayBytes`).  The latter states the encoded value
  in terms of the model's `Commitment.contestDelay` field;
* the encoding is injective on the BOLT-valid delay range `d < 2^16`, hence
  distinct delays give distinct witness scripts
  (`waveD_d42_toLocal_commits_delay`) and, under an injective hash, distinct
  `to_local` output scripts (`waveD_d42_toLocal_output_commits_delay`);
* the `to_local` output of `commitmentOutputs` is unconditionally
  `p2wsh (sha256 <delay-carrying witness script>)` under `HashesMatch`
  (`waveD_d42_commitmentOutputs_toLocal_witnessProgram`).

Negative/fidelity results:

* the fixed-width encoding truncates: delay `0` and delay `65536` produce the
  *same* script (`waveD_d42_toLocal_delay_truncation_counterexample`), so the
  range hypothesis in the injectivity theorem cannot be dropped.  This is
  harmless for the protocol because BOLT 2 carries `to_self_delay` as a
  `u16` field (0..65535), see below;
* BOLT 3 uses minimal `CScriptNum` encoding, while the model always uses a
  three-byte push.  The model is byte-identical to a minimal encoding only for
  `128 ≤ d < 32768`: `d = 0` uses `OP_0`, `1 ≤ d < 128` uses a shorter push,
  and `d ≥ 32768` needs an extra sign byte.  The value represented is still
  exactly `d`; no script interpreter is modelled here, so this is a
  byte-template statement only;
* `SHA256` is not modelled.  `HashesMatch` is a `Prop` parameter, and the
  output-level commitment theorem assumes injectivity of the supplied hash.
  This is the missing crypto bridge, not an extra protocol hypothesis.

BOLT anchors pinned at `refs/bolts` commit
`1aadb719b4007c4cea0ba6e36b08c4fb53788dee`:

* BOLT 3 `03-transactions.md:113-135` (`to_local` output), `:136-147`
  (`to_remote`), `:305-354` (dust/trimming).
* BOLT 2 `02-peer-protocol.md:697` and `:921` — `to_self_delay` is a `u16` in
  `open_channel` / `accept_channel`; `:750-752` explains that it delays the
  *other* party's `to_local` output (the local/remote asymmetry).

LDK anchor at `fe4900930c6bd5786ec4203274d7cf312776a5a6`:
`lightning/src/ln/chan_utils.rs:687-700`
(`get_revokeable_redeemscript`, the `OP_IF ... OP_ELSE to_self_delay OP_CSV
OP_DROP ...` template) and `:1614-1740` (`CommitmentTransaction`, which fixes
the CSV delay from the counterparty's `to_self_delay`).
-/

namespace LnLean.Proofs.WaveD.D42

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean LnLean.Bitcoin
open LnLean.Proofs.Bitcoin

-- OBLIGATION: LN-WD-D42

/-! ## The delay-carrying pieces of the `to_local` witness script -/

/-- Everything before the CSV-delay push in the `to_local` witness script:
`OP_IF <revocationpubkey> OP_ELSE`. -/
def toLocalDelayPrefix (revocationKey : PubKey) : ByteArray :=
  ByteArray.empty.push OP_IF ++ pushData revocationKey.bytes ++
    ByteArray.empty.push OP_ELSE

/-- Everything after the CSV-delay push in the `to_local` witness script:
`OP_CSV OP_DROP <local_delayedpubkey> OP_ENDIF OP_CHECKSIG`.  Written
right-associated so that byte-index reasoning can peel it one push at a
time. -/
def toLocalDelaySuffix (delayedPaymentKey : PubKey) : ByteArray :=
  ByteArray.empty.push OP_CSV ++
    (ByteArray.empty.push OP_DROP ++
      (pushData delayedPaymentKey.bytes ++
        (ByteArray.empty.push OP_ENDIF ++ ByteArray.empty.push OP_CHECKSIG)))

/-- The `to_local` witness script is exactly a fixed prefix, the encoded
`to_self_delay`, and a fixed suffix; only two key pushes and the delay push
occur. -/
theorem waveD_d42_toLocal_decomp (revocationKey delayedPaymentKey : PubKey)
    (toSelfDelay : Blocks) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes =
      toLocalDelayPrefix revocationKey ++ pushScriptNum16 toSelfDelay ++
        toLocalDelaySuffix delayedPaymentKey := by
  unfold toLocalWitnessScript toLocalDelayPrefix toLocalDelaySuffix
  simp only [ByteArray.append_assoc]

/-- The `to_local` witness script contains the encoded `to_self_delay` as a
contiguous byte substring. -/
theorem waveD_d42_toLocal_contains_delayPush
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks) :
    ScriptProps.BytesContain
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes
      (pushScriptNum16 toSelfDelay) :=
  ⟨toLocalDelayPrefix revocationKey, toLocalDelaySuffix delayedPaymentKey,
    waveD_d42_toLocal_decomp revocationKey delayedPaymentKey toSelfDelay⟩

/-! ## The exact byte value of the delay push -/

/-- `pushUInt16LE n` is the little-endian byte pair
`[n % 256, (n / 256) % 256]` (specified as a list of `Nat` values so that the
value is independent of `UInt8` representation details). -/
theorem waveD_d42_pushUInt16LE_data_toList (n : Nat) :
    (pushUInt16LE n).data.toList.map UInt8.toNat = [n % 256, (n / 256) % 256] := by
  unfold pushUInt16LE
  simp [Nat.shiftRight_eq_div_pow]

/-- `pushScriptNum16 n` is the three-byte push
`[0x02, n % 256, (n / 256) % 256]`; the leading `2` is the push length that
`pushData` prepends. -/
theorem waveD_d42_pushScriptNum16_data_toList (n : Nat) :
    (pushScriptNum16 n).data.toList.map UInt8.toNat = [2, n % 256, (n / 256) % 256] := by
  unfold pushScriptNum16 pushData
  rw [ByteArray.data_append, Array.toList_append, List.map_append]
  rw [waveD_d42_pushUInt16LE_data_toList n]
  have h2 : (pushUInt16LE n).size = 2 := by
    unfold pushUInt16LE
    simp
  simp [h2]

/-- The fixed-width relative-timelock encoding always has size two. -/
theorem waveD_d42_pushUInt16LE_size (n : Nat) : (pushUInt16LE n).size = 2 := by
  unfold pushUInt16LE
  simp

/-- The delay push always has size three: a one-byte push length plus the
two-byte little-endian value. -/
theorem waveD_d42_pushScriptNum16_size (n : Nat) : (pushScriptNum16 n).size = 3 := by
  unfold pushScriptNum16 pushData
  simp [waveD_d42_pushUInt16LE_size]

/-! ## Byte-index helpers (local to this module) -/

private theorem waveD_d42_getElem?_append_lt (a b : ByteArray) (i : Nat)
    (h : i < a.size) : (a ++ b)[i]? = a[i]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append, ite_eq_left (by simpa using h)]
  rw [show a[i]? = a.data[i]? from rfl]

private theorem waveD_d42_getElem?_append_ge (a b : ByteArray) (i : Nat)
    (h : a.size ≤ i) : (a ++ b)[i]? = b[i - a.size]? := by
  rw [show (a ++ b)[i]? = (a ++ b).data[i]? from rfl,
      ByteArray.data_append, Array.getElem?_append, ite_eq_right (by simpa using h)]
  rw [show b[i - a.size]? = b.data[i - a.size]? from rfl]
  rfl

private theorem waveD_d42_getElem?_push_eq (a : ByteArray) (x : UInt8) :
    (a.push x)[a.size]? = some x := by
  rw [show (a.push x)[a.size]? = (a.push x).data[a.size]? from rfl,
      ByteArray.data_push, Array.getElem?_push,
      ite_eq_left (show a.size = a.data.size from rfl)]

private theorem waveD_d42_getElem?_push_lt (a : ByteArray) (x : UInt8) (i : Nat)
    (h : i < a.size) : (a.push x)[i]? = a[i]? := by
  rw [show (a.push x)[i]? = (a.push x).data[i]? from rfl,
      ByteArray.data_push, Array.getElem?_push,
      ite_eq_right (by simpa using Nat.ne_of_lt h)]
  rw [show a[i]? = a.data[i]? from rfl]

private theorem waveD_d42_pushUInt16LE_getElem?_zero (n : Nat) :
    (pushUInt16LE n)[0]? = some n.toUInt8 := by
  unfold pushUInt16LE
  rw [waveD_d42_getElem?_push_lt _ _ _ (by simp)]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  exact waveD_d42_getElem?_push_eq _ _

private theorem waveD_d42_pushUInt16LE_getElem?_one (n : Nat) :
    (pushUInt16LE n)[1]? = some (n >>> 8).toUInt8 := by
  unfold pushUInt16LE
  rw [show (1 : Nat) = (ByteArray.empty.push n.toUInt8).size from by simp]
  exact waveD_d42_getElem?_push_eq _ _

private theorem waveD_d42_getElem?_pushData_len (pre k rest : ByteArray) :
    (pre ++ pushData k ++ rest)[pre.size]? = some k.size.toUInt8 := by
  unfold pushData
  rw [waveD_d42_getElem?_append_lt
    (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k)) rest pre.size
    (by simp only [ByteArray.size_append, ByteArray.size_push]; omega)]
  rw [waveD_d42_getElem?_append_ge pre (ByteArray.empty.push k.size.toUInt8 ++ k)
    pre.size (by omega)]
  simp only [Nat.sub_self]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  rw [waveD_d42_getElem?_append_lt (ByteArray.empty.push k.size.toUInt8) k
    ByteArray.empty.size
    (by simp only [ByteArray.size_push, ByteArray.size_empty]; omega)]
  exact waveD_d42_getElem?_push_eq _ _

private theorem waveD_d42_getElem?_pushData_key (pre k rest : ByteArray) (j : Nat)
    (hj : j < k.size) : (pre ++ pushData k ++ rest)[pre.size + 1 + j]? = k[j]? := by
  unfold pushData
  rw [waveD_d42_getElem?_append_lt
    (pre ++ (ByteArray.empty.push k.size.toUInt8 ++ k)) rest (pre.size + 1 + j)
    (by simp only [ByteArray.size_append, ByteArray.size_push]; omega)]
  rw [waveD_d42_getElem?_append_ge pre (ByteArray.empty.push k.size.toUInt8 ++ k)
    (pre.size + 1 + j) (by omega)]
  rw [show pre.size + 1 + j - pre.size = 1 + j from by omega]
  rw [waveD_d42_getElem?_append_ge (ByteArray.empty.push k.size.toUInt8) k (1 + j)
    (by simp only [ByteArray.size_push, ByteArray.size_empty]; omega)]
  rw [show (ByteArray.empty.push k.size.toUInt8).size = 1 from by simp]
  rw [show 1 + j - 1 = j from by omega]

private theorem waveD_d42_getElem?_after (a b : ByteArray) (k : Nat) :
    (a ++ b)[a.size + k]? = b[k]? := by
  rw [waveD_d42_getElem?_append_ge a b (a.size + k) (by omega)]
  congr 1
  omega

/-! ## Fixed offsets of the delay and the CSV opcodes -/

/-- With a 33-byte compressed revocation key the delay prefix is 36 bytes:
`OP_IF` (1) + `pushData key` (34) + `OP_ELSE` (1). -/
theorem waveD_d42_toLocalDelayPrefix_size (revocationKey : PubKey)
    (h : revocationKey.bytes.size = 33) :
    (toLocalDelayPrefix revocationKey).size = 36 := by
  unfold toLocalDelayPrefix
  simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty,
    ScriptProps.pushData_size, h]

private theorem waveD_d42_toLocalDelaySuffix_zero (delayedPaymentKey : PubKey) :
    (toLocalDelaySuffix delayedPaymentKey)[0]? = some OP_CSV := by
  unfold toLocalDelaySuffix
  rw [waveD_d42_getElem?_append_lt _ _ 0 (by simp)]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  exact waveD_d42_getElem?_push_eq _ _

private theorem waveD_d42_toLocalDelaySuffix_one (delayedPaymentKey : PubKey) :
    (toLocalDelaySuffix delayedPaymentKey)[1]? = some OP_DROP := by
  unfold toLocalDelaySuffix
  rw [waveD_d42_getElem?_append_ge _ _ 1 (by simp)]
  rw [show (1 : Nat) - (ByteArray.empty.push OP_CSV).size = 0 from by simp]
  rw [waveD_d42_getElem?_append_lt (ByteArray.empty.push OP_DROP) _ 0 (by simp)]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  exact waveD_d42_getElem?_push_eq _ _

/-- Byte 36 is the push-length byte `0x02` of the two-byte delay push. -/
theorem waveD_d42_toLocal_delayPush_length
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[36]? =
      some 2 := by
  rw [waveD_d42_toLocal_decomp,
    ← waveD_d42_toLocalDelayPrefix_size revocationKey h]
  unfold pushScriptNum16
  exact waveD_d42_getElem?_pushData_len _ _ _

/-- Byte 37 is the low byte of the little-endian delay. -/
theorem waveD_d42_toLocal_delay_lowByte
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[37]? =
      some toSelfDelay.toUInt8 := by
  rw [waveD_d42_toLocal_decomp]
  have h37 : (37 : Nat) = (toLocalDelayPrefix revocationKey).size + 1 + 0 := by
    rw [waveD_d42_toLocalDelayPrefix_size revocationKey h]
  rw [h37]
  unfold pushScriptNum16
  rw [waveD_d42_getElem?_pushData_key _ _ _ 0 (by simp [pushUInt16LE])]
  exact waveD_d42_pushUInt16LE_getElem?_zero toSelfDelay

/-- Byte 38 is the high byte of the little-endian delay. -/
theorem waveD_d42_toLocal_delay_highByte
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[38]? =
      some (toSelfDelay >>> 8).toUInt8 := by
  rw [waveD_d42_toLocal_decomp]
  have h38 : (38 : Nat) = (toLocalDelayPrefix revocationKey).size + 1 + 1 := by
    rw [waveD_d42_toLocalDelayPrefix_size revocationKey h]
  rw [h38]
  unfold pushScriptNum16
  rw [waveD_d42_getElem?_pushData_key _ _ _ 1 (by simp [pushUInt16LE])]
  exact waveD_d42_pushUInt16LE_getElem?_one toSelfDelay

/-- Byte 39, immediately after the delay push, is `OP_CSV` (`0xb2`). -/
theorem waveD_d42_toLocal_csvOpcode
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[39]? =
      some OP_CSV := by
  rw [waveD_d42_toLocal_decomp]
  have h39 : (39 : Nat) =
      (toLocalDelayPrefix revocationKey ++ pushScriptNum16 toSelfDelay).size + 0 := by
    rw [ByteArray.size_append, waveD_d42_toLocalDelayPrefix_size revocationKey h,
      waveD_d42_pushScriptNum16_size]
  rw [h39, waveD_d42_getElem?_after]
  exact waveD_d42_toLocalDelaySuffix_zero delayedPaymentKey

/-- Byte 40 is `OP_DROP` (`0x75`), completing `<delay> OP_CSV OP_DROP`. -/
theorem waveD_d42_toLocal_dropOpcode
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[40]? =
      some OP_DROP := by
  rw [waveD_d42_toLocal_decomp]
  have h40 : (40 : Nat) =
      (toLocalDelayPrefix revocationKey ++ pushScriptNum16 toSelfDelay).size + 1 := by
    rw [ByteArray.size_append, waveD_d42_toLocalDelayPrefix_size revocationKey h,
      waveD_d42_pushScriptNum16_size]
  rw [h40, waveD_d42_getElem?_after]
  exact waveD_d42_toLocalDelaySuffix_one delayedPaymentKey

/-- The exact opcode/value representation of the delay in the model:
bytes 36..40 are `0x02, d % 256, (d / 256) % 256, OP_CSV, OP_DROP`. -/
theorem waveD_d42_toLocal_delay_encoding
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[36]? =
        some 2 ∧
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[37]? =
        some toSelfDelay.toUInt8 ∧
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[38]? =
        some (toSelfDelay >>> 8).toUInt8 ∧
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[39]? =
        some OP_CSV ∧
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[40]? =
        some OP_DROP :=
  ⟨waveD_d42_toLocal_delayPush_length revocationKey delayedPaymentKey toSelfDelay h,
   waveD_d42_toLocal_delay_lowByte revocationKey delayedPaymentKey toSelfDelay h,
   waveD_d42_toLocal_delay_highByte revocationKey delayedPaymentKey toSelfDelay h,
   waveD_d42_toLocal_csvOpcode revocationKey delayedPaymentKey toSelfDelay h,
   waveD_d42_toLocal_dropOpcode revocationKey delayedPaymentKey toSelfDelay h⟩

/-- The two delay bytes, read back as `Nat` values, are exactly
`d % 256` and `(d / 256) % 256`: the script's bytes determine the represented
delay (modulo the 16-bit width). -/
theorem waveD_d42_toLocal_delayBytes_toNat
    (revocationKey delayedPaymentKey : PubKey) (toSelfDelay : Blocks)
    (h : revocationKey.bytes.size = 33) :
    ∃ b0 b1 : UInt8,
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[37]? =
        some b0 ∧
      (toLocalWitnessScript revocationKey delayedPaymentKey toSelfDelay).bytes[38]? =
        some b1 ∧
      b0.toNat = toSelfDelay % 256 ∧ b1.toNat = (toSelfDelay / 256) % 256 := by
  refine ⟨toSelfDelay.toUInt8, (toSelfDelay >>> 8).toUInt8,
    waveD_d42_toLocal_delay_lowByte revocationKey delayedPaymentKey toSelfDelay h,
    waveD_d42_toLocal_delay_highByte revocationKey delayedPaymentKey toSelfDelay h,
    ?_, ?_⟩
  · simp
  · rw [Nat.shiftRight_eq_div_pow]
    simp

/-- Bytes 37/38 of the `to_local` witness script encode
`Commitment.contestDelay` exactly when the parameters use that delay. -/
theorem waveD_d42_contestDelay_delayBytes
    (c : LnLean.Channel.Commitment) (p : CommitmentParams)
    (hdelay : p.toSelfDelay = c.contestDelay)
    (h : p.revocationKey.bytes.size = 33) :
    ∃ b0 b1 : UInt8,
      (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes[37]? =
        some b0 ∧
      (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay).bytes[38]? =
        some b1 ∧
      b0.toNat = c.contestDelay % 256 ∧
      b1.toNat = (c.contestDelay / 256) % 256 := by
  obtain ⟨b0, b1, h0, h1, hv0, hv1⟩ :=
    waveD_d42_toLocal_delayBytes_toNat p.revocationKey p.delayedPaymentKey
      p.toSelfDelay h
  exact ⟨b0, b1, h0, h1, by rw [hv0, hdelay], by rw [hv1, hdelay]⟩

/-! ## Injectivity of the delay encoding -/

/-- The fixed two-byte little-endian encoding determines the delay modulo
`2^16`. -/
theorem waveD_d42_pushUInt16LE_mod_eq {a b : Nat}
    (h : pushUInt16LE a = pushUInt16LE b) : a % 65536 = b % 65536 := by
  have hlist : (pushUInt16LE a).data.toList.map UInt8.toNat =
      (pushUInt16LE b).data.toList.map UInt8.toNat := by rw [h]
  rw [waveD_d42_pushUInt16LE_data_toList a,
    waveD_d42_pushUInt16LE_data_toList b] at hlist
  simp only [List.cons.injEq] at hlist
  obtain ⟨h0, h1⟩ := hlist
  omega

/-- The two-byte little-endian encoding is injective on `[0, 2^16)`. -/
theorem waveD_d42_pushUInt16LE_injective {a b : Nat}
    (ha : a < 2^16) (hb : b < 2^16)
    (h : pushUInt16LE a = pushUInt16LE b) : a = b := by
  have hmod := waveD_d42_pushUInt16LE_mod_eq h
  omega

/-- The delay push determines the delay modulo `2^16`. -/
theorem waveD_d42_pushScriptNum16_mod_eq {a b : Nat}
    (h : pushScriptNum16 a = pushScriptNum16 b) : a % 65536 = b % 65536 := by
  have hs : (pushUInt16LE a).size = (pushUInt16LE b).size := by
    rw [waveD_d42_pushUInt16LE_size, waveD_d42_pushUInt16LE_size]
  have hx : pushUInt16LE a = pushUInt16LE b := by
    unfold pushScriptNum16 pushData at h
    rw [hs] at h
    exact (ByteArray.append_right_inj
      (ByteArray.empty.push (pushUInt16LE b).size.toUInt8)).mp h
  exact waveD_d42_pushUInt16LE_mod_eq hx

/-- The delay push is injective on `[0, 2^16)`. -/
theorem waveD_d42_pushScriptNum16_injective {a b : Nat}
    (ha : a < 2^16) (hb : b < 2^16)
    (h : pushScriptNum16 a = pushScriptNum16 b) : a = b := by
  have hmod := waveD_d42_pushScriptNum16_mod_eq h
  omega

/-! ## The `to_local` witness script commits to the delay -/

/-- Equal `to_local` witness scripts (same keys) have equal delay pushes. -/
theorem waveD_d42_toLocal_delay_push_eq
    (revocationKey delayedPaymentKey : PubKey) {d₁ d₂ : Blocks}
    (h : toLocalWitnessScript revocationKey delayedPaymentKey d₁ =
      toLocalWitnessScript revocationKey delayedPaymentKey d₂) :
    pushScriptNum16 d₁ = pushScriptNum16 d₂ := by
  have hb : (toLocalWitnessScript revocationKey delayedPaymentKey d₁).bytes =
      (toLocalWitnessScript revocationKey delayedPaymentKey d₂).bytes :=
    congrArg (fun s : Script => s.bytes) h
  unfold toLocalWitnessScript at hb
  simp only [ByteArray.append_assoc] at hb
  simpa only [ByteArray.append_right_inj, ByteArray.append_left_inj] using hb

/-- Equal `to_local` witness scripts (same keys) represent the same delay
modulo the 16-bit width of the model's encoding. -/
theorem waveD_d42_toLocal_delay_congr
    (revocationKey delayedPaymentKey : PubKey) {d₁ d₂ : Blocks}
    (h : toLocalWitnessScript revocationKey delayedPaymentKey d₁ =
      toLocalWitnessScript revocationKey delayedPaymentKey d₂) :
    d₁ % 65536 = d₂ % 65536 :=
  waveD_d42_pushScriptNum16_mod_eq
    (waveD_d42_toLocal_delay_push_eq revocationKey delayedPaymentKey h)

/-- **The `to_local` witness script commits to the CSV delay.**  Two
distinct delays in the BOLT-valid range `[0, 2^16)` give distinct witness
scripts when the keys are held fixed. -/
theorem waveD_d42_toLocal_commits_delay
    (revocationKey delayedPaymentKey : PubKey) {d₁ d₂ : Blocks}
    (h1 : d₁ < 2^16) (h2 : d₂ < 2^16) (hne : d₁ ≠ d₂) :
    toLocalWitnessScript revocationKey delayedPaymentKey d₁ ≠
      toLocalWitnessScript revocationKey delayedPaymentKey d₂ := by
  intro h
  exact hne (waveD_d42_pushScriptNum16_injective h1 h2
    (waveD_d42_toLocal_delay_push_eq revocationKey delayedPaymentKey h))

/-- **Negative result.**  The fixed-width encoding truncates, so delays
`0` and `65536` give the *same* `to_local` witness script.  The range
hypothesis in `waveD_d42_toLocal_commits_delay` is therefore necessary; it is
discharged in the protocol by BOLT 2's `u16` `to_self_delay` field. -/
theorem waveD_d42_toLocal_delay_truncation_counterexample :
    ∃ d₁ d₂ : Blocks, d₁ ≠ d₂ ∧
      toLocalWitnessScript ⟨ByteArray.empty⟩ ⟨ByteArray.empty⟩ d₁ =
        toLocalWitnessScript ⟨ByteArray.empty⟩ ⟨ByteArray.empty⟩ d₂ := by
  refine ⟨0, 65536, by decide, ?_⟩
  have hx : pushScriptNum16 0 = pushScriptNum16 65536 := by decide
  unfold toLocalWitnessScript
  rw [hx]

/-! ## From the witness script to the on-chain `to_local` output -/

/-- `toLocalScriptPubKey` is injective in its witness-program argument: a
P2WSH output determines its 32-byte program. -/
theorem waveD_d42_toLocalScriptPubKey_injective {h₁ h₂ : ByteArray}
    (h : toLocalScriptPubKey h₁ = toLocalScriptPubKey h₂) : h₁ = h₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  unfold toLocalScriptPubKey p2wsh at hb
  exact (ByteArray.append_right_inj ((ByteArray.empty.push OP_0).push 0x20)).mp hb

/-- `commitmentOutputs` contains a `toLocal` output whose script is the P2WSH
of the stored witness-script hash. -/
theorem waveD_d42_commitmentOutputs_toLocal_output (p : CommitmentParams) :
    ∃ o ∈ commitmentOutputs p, o.kind = OutputKind.toLocal ∧
      o.scriptPubKey = toLocalScriptPubKey p.toLocalWitnessScriptHash := by
  have hmem : CommitmentOutput.mk OutputKind.toLocal p.toLocalValue
      (toLocalScriptPubKey p.toLocalWitnessScriptHash) ∈ commitmentOutputs p := by
    simp [commitmentOutputs]
  exact ⟨_, hmem, rfl, rfl⟩

/-- Under the model's `HashesMatch` hypothesis, the `to_local` output is the
P2WSH of the SHA256 of the delay-carrying witness script.  This links the
parameter `p.toSelfDelay` to the on-chain output without assuming anything
about SHA256. -/
theorem waveD_d42_commitmentOutputs_toLocal_witnessProgram
    (p : CommitmentParams) (sha256 : Script → ByteArray) (hp : p.HashesMatch sha256) :
    ∃ o ∈ commitmentOutputs p, o.kind = OutputKind.toLocal ∧
      o.scriptPubKey = p2wsh (sha256
        (toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay)) := by
  obtain ⟨o, ho, hk, hs⟩ := waveD_d42_commitmentOutputs_toLocal_output p
  refine ⟨o, ho, hk, ?_⟩
  rw [hs, toLocalScriptPubKey, hp.1]

/-- **The on-chain `to_local` output commits to the CSV delay**, conditional on
the missing crypto bridge: if the supplied `sha256` is injective, then two
parameter sets with the same keys but distinct BOLT-valid delays have distinct
`to_local` output scripts. -/
theorem waveD_d42_toLocal_output_commits_delay
    (sha256 : Script → ByteArray)
    (hinj : ∀ s₁ s₂ : Script, sha256 s₁ = sha256 s₂ → s₁ = s₂)
    (p q : CommitmentParams) (hp : p.HashesMatch sha256) (hq : q.HashesMatch sha256)
    (hrev : p.revocationKey = q.revocationKey)
    (hdel : p.delayedPaymentKey = q.delayedPaymentKey)
    (h1 : p.toSelfDelay < 2^16) (h2 : q.toSelfDelay < 2^16)
    (hne : p.toSelfDelay ≠ q.toSelfDelay) :
    toLocalScriptPubKey p.toLocalWitnessScriptHash ≠
      toLocalScriptPubKey q.toLocalWitnessScriptHash := by
  intro hspk
  have hhash : p.toLocalWitnessScriptHash = q.toLocalWitnessScriptHash :=
    waveD_d42_toLocalScriptPubKey_injective hspk
  rw [hp.1, hq.1] at hhash
  have hs : toLocalWitnessScript p.revocationKey p.delayedPaymentKey p.toSelfDelay =
      toLocalWitnessScript q.revocationKey q.delayedPaymentKey q.toSelfDelay :=
    hinj _ _ hhash
  rw [hrev, hdel] at hs
  exact hne (waveD_d42_pushScriptNum16_injective h1 h2
    (waveD_d42_toLocal_delay_push_eq q.revocationKey q.delayedPaymentKey hs))

end LnLean.Proofs.WaveD.D42
