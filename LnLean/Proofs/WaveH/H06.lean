import LnLean.Proofs.Bitcoin.SequenceContextTargets

/-!
# Wave 8 / H06 — the `csv ≥ 32768` boundary of the fixed-width `delayBytes`

Lane `H06` (`L1-02`, `L1-07`).  Wave 7 (`SequenceContextTargets`) proves the
exact BIP 68/112 sequence-context refinement for the delayed `to_local`
branch under the hypothesis `csv < 32768`.  This module closes the boundary
question around that hypothesis for the *fixed-width* two-byte payload
`delayBytes csv = [csv % 256, (csv / 256) % 256]`:

* **Exact decoding at and above the boundary.**  `ScriptNum` is little-endian
  *sign-magnitude*, so the high byte `0x80…0xff` is a sign byte.  For
  `32768 ≤ csv < 65536` the payload decodes to `-(csv - 32768)`, not `csv`
  (`decodeNum_delayBytes_ge`); at exactly `32768` it decodes to `0`
  (`decodeNum_delayBytes_32768`), i.e. the nominal delay silently collapses
  to the empty delay.

* **The out-of-range branch is not representable.**  Every two-byte payload
  with byte digits decodes strictly between `-32768` and `32768`
  (`setVchBE_length_le_two_abs`), so no two-byte encoding decodes to a
  non-negative value `≥ 32768` (`no_two_digit_nonneg_encoding`).  The canonical
  minimal `CScriptNum` encoding of such a delay needs at least three bytes
  (`scriptNumBE_length_ge_three`, `encodeScriptNum_delay_size_ge_three`).
  Consequently `decodeNum (delayBytes csv) = .ok csv ↔ csv < 32768`
  (`decodeNum_delayBytes_self_iff`), the exact faithful-domain statement.

* **The `u16` field is wider than the faithful script number.**  `delayBytes`
  is the low 16 bits of `csv` (`delayBytes_mod`), so it is not injective
  (`delayBytes_not_injective`): `0` and `65536` share a payload.

* **The disable-bit boundary.**  The BIP 68 *operand* disable bit (bit 31) can
  never be set by a two-byte payload (`disableBit_setVchBE_two`,
  `disableBit_decodeNum_delayBytes`), so the BIP 112 “operand disable bit ⇒
  NOP” branch of `OP_CSV` is unreachable through `delayBytes`
  (`opCsv_disable_nop_unreachable`).  This removes the `csv < 32768`
  hypothesis from the wave-7 `disableBit_delay` lemma.

* **Vendor behaviour at the boundary.**  `OP_CSV` rejects a *negative* decoded
  operand with `.error .negativeLocktime` (`dispatchOp_csv_negative`), so for
  `32768 < csv < 65536` the delayed branch can never execute
  (`dispatchOp_csv_delayBytes_neg`).  For `csv = 32768` the operand is `0` and
  the branch runs the sequence check on `0`
  (`toLocal_delayed_boundary_32768_vendor_iff`).

* **The wave-7 range hypothesis is necessary.**  `boundary_nominal_context_fails`
  keeps the sharp counterexample: with a height-domain transaction sequence
  whose masked value is below `32768`, the vendor accepts the `csv = 32768`
  witness (given the delayed-key signature) while the *nominal* context claim
  `32768 ≤ masked sequence` is false.  The nominal statement is only true for
  the decoded operand, which is `0` there.

Scope caveat: BOLT 3 requires *minimal* `CScriptNum` encoding, so a faithful
implementation encodes a delay in `[32768, 65535]` with three bytes.  The
counterexample is therefore a limitation of this model's fixed-width
two-byte `delayBytes`, not a claim about mainnet consensus.  The range
hypothesis `csv < 32768` is exactly the domain on which the model's payload is
a faithful script number.
-/

namespace LnLean.Proofs.WaveH.H06

set_option autoImplicit false

open Bitcoin.Data
open Bitcoin.Activation
open Bitcoin.Script.Parser
open Bitcoin.Interpreter
open Bitcoin.Numeric
open LnLean
open LnLean.Bitcoin
open LnLean.Proofs.Bitcoin.SpendTargets
open LnLean.Proofs.Bitcoin.InterpreterBridgeTargets
open LnLean.Proofs.Bitcoin.InterpreterRevocationTargets
open LnLean.Proofs.Bitcoin.SighashBridgeTargets
open LnLean.Proofs.Bitcoin.SequenceContextTargets

/-! ## 1. Exact decoding at and above the sign boundary -/

/-- The value of the two-byte little-endian payload at and above the sign
boundary: the high byte is at least `0x80`, so `setVchBE` reads it as a
sign-magnitude negative number `-(csv - 32768)`. -/
theorem setVchBE_delay_ge (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    setVchBE [(csv >>> 8) % 256, csv % 256] = -(((csv - 32768 : Nat)) : Int) := by
  have hdiv : csv >>> 8 = csv / 256 := Nat.shiftRight_eq_div_pow csv 8
  have hhi' : (csv >>> 8) % 256 = csv / 256 := by
    rw [hdiv]
    exact Nat.mod_eq_of_lt (by omega)
  have hge : ¬ ((csv >>> 8) % 256 < 128) := by
    rw [hhi']
    omega
  simp only [setVchBE, hge, ite_false, magOfBE, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.add_zero, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
  rw [hhi']
  have hsub : (csv / 256 - 128) * 256 + csv % 256 = csv - 32768 := by
    have hdm : csv / 256 * 256 + csv % 256 = csv := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod csv 256
    have hge : 128 ≤ csv / 256 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 256)]
      omega
    have hX : 32768 ≤ csv / 256 * 256 := Nat.mul_le_mul_right 256 hge
    rw [Nat.sub_mul, (by decide : 128 * 256 = 32768)]
    have h1 : csv / 256 * 256 - 32768 + csv % 256 =
        csv / 256 * 256 + csv % 256 - 32768 := (Nat.sub_add_comm hX).symm
    rw [h1, hdm]
  rw [hsub]

/-- `decodeBE` on the reversed delay bytes returns the sign-magnitude value
`-(csv - 32768)` for `32768 ≤ csv < 65536`. -/
theorem decodeBE_delay_ge (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    decodeBE false 5 (bytesOf (delayBytes csv)).reverse =
      some (-(((csv - 32768 : Nat)) : Int)) := by
  rw [bytesOf_delayBytes]
  have hlen : ([(csv >>> 8) % 256, csv % 256] : List Nat).length ≤ 5 := by simp
  rw [show (([csv % 256, (csv >>> 8) % 256] : List Nat).reverse) =
      [(csv >>> 8) % 256, csv % 256] by rfl]
  rw [decodeBE_some hlen (Or.inl rfl), setVchBE_delay_ge csv hlo hhi]

/-- **Exact out-of-range decoding.**  For `32768 ≤ csv < 65536` the fixed-width
payload decodes to `-(csv - 32768)`, not to `csv`. -/
theorem decodeNum_delayBytes_ge (pol : PolicyFlags) (hmin : pol.minimalData = false)
    (csv : Nat) (hlo : 32768 ≤ csv) (hhi : csv < 65536) :
    decodeNum pol (delayBytes csv) 5 = .ok (-(((csv - 32768 : Nat)) : Int)) := by
  rw [decodeNum, decodeScriptNum, hmin, decodeBE_delay_ge csv hlo hhi]

/-- At exactly `32768` the payload is `0x80 0x00`, which decodes to `0`: the
nominal delay silently collapses to the empty delay. -/
theorem decodeNum_delayBytes_32768 :
    decodeNum ({} : PolicyFlags) (delayBytes 32768) 5 = .ok (0 : Int) := by
  have h := decodeNum_delayBytes_ge ({} : PolicyFlags) (by decide) 32768 (by decide)
    (by decide)
  simpa using h

/-- At exactly `32768` the decoded operand is the non-negative `0`, so `OP_CSV`
does not reject it as a negative locktime — it runs the sequence check on
`0`. -/
theorem dispatchOp_csv_delayBytes_32768_nonneg (ctx : Ctx) (st : State)
    (htop : topAt st.stack 1 = delayBytes 32768)
    (hmin : ctx.pol.minimalData = false) :
    decodeNum ctx.pol (topAt st.stack 1) 5 = .ok (0 : Int) := by
  rw [decodeNum_policy_congr ctx.pol ({} : PolicyFlags) hmin, htop]
  exact decodeNum_delayBytes_32768

/-! ## 2. The faithful domain of the two-byte payload -/

theorem delayBytes_bytes_length (csv : Nat) :
    (bytesOf (toLocalDelayBytes csv)).reverse.length = 2 := by
  rw [List.length_reverse, bytesOf_length]
  exact toLocalDelayBytes_size csv

theorem delayBytes_bytes_length_le (csv : Nat) :
    (bytesOf (toLocalDelayBytes csv)).reverse.length ≤ 2 := by
  have h := delayBytes_bytes_length csv
  omega

/-- **Two-byte representability.**  A two-digit (or shorter) sign-magnitude
payload with byte digits decodes strictly inside `(-32768, 32768)`. -/
theorem setVchBE_length_le_two_abs (l : List Nat) (hlen : l.length ≤ 2)
    (hdig : ∀ d ∈ l, d < 256) :
    -(32768 : Int) < setVchBE l ∧ setVchBE l < 32768 := by
  match l with
  | [] => decide
  | [d] =>
      have hd : d < 256 := hdig d (by simp)
      simp only [setVchBE, magOfBE, List.length_nil, Nat.pow_zero,
        Nat.mul_one]
      split <;> omega
  | [d, e] =>
      have hd : d < 256 := hdig d (by simp)
      have he : e < 256 := hdig e (by simp)
      simp only [setVchBE, magOfBE, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.pow_zero, Nat.pow_one, Nat.mul_one]
      split <;> omega
  | d :: e :: f :: t =>
      simp only [List.length_cons] at hlen
      omega

/-- No two-byte payload decodes to a non-negative value at or above `32768`.
This is why the `csv ≥ 32768` branch cannot be represented by the faithful
two-byte encoding: it needs a third byte. -/
theorem no_two_digit_nonneg_encoding (csv : Nat) (hcsv : 32768 ≤ csv)
    (l : List Nat) (hlen : l.length ≤ 2) (hdig : ∀ d ∈ l, d < 256)
    (h : setVchBE l = (csv : Int)) : False := by
  have hb := (setVchBE_length_le_two_abs l hlen hdig).2
  omega

/-- Any successful decode of the two-byte payload lands in the two-byte
sign-magnitude window `(-32768, 32768)`, for every policy word. -/
theorem decodeNum_delayBytes_range (pol : PolicyFlags) (csv : Nat) (n : Int)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n) :
    -(32768 : Int) < n ∧ n < 32768 := by
  have h : decodeScriptNum (toLocalDelayBytes csv) pol.minimalData 5 = some n := by
    cases hd : decodeScriptNum (toLocalDelayBytes csv) pol.minimalData 5 with
    | none => simp [decodeNum, hd] at hdec
    | some m =>
        have hmn : m = n := by simpa [decodeNum, hd] using hdec
        simp [hmn]
  have hlen : (bytesOf (toLocalDelayBytes csv)).reverse.length ≤ 5 := by
    have h2 := delayBytes_bytes_length_le csv
    omega
  rw [decodeScriptNum] at h
  unfold decodeBE at h
  rw [ite_eq_right (show ¬ (bytesOf (toLocalDelayBytes csv)).reverse.length > 5 from by omega)] at h
  split at h
  · simp at h
  · have hn : n = setVchBE (bytesOf (delayBytes csv)).reverse :=
      (Option.some.inj h).symm
    rw [hn]
    exact setVchBE_length_le_two_abs _
      (by exact delayBytes_bytes_length_le csv)
      (by
        intro d hd
        rw [List.mem_reverse] at hd
        exact bytesOf_lt _ d hd)

/-- The delay payload never decodes back to a nominal value `≥ 32768`. -/
theorem delayBytes_decode_never_above (csv : Nat) (hcsv : 32768 ≤ csv) :
    setVchBE (bytesOf (delayBytes csv)).reverse ≠ (csv : Int) := by
  intro h
  exact no_two_digit_nonneg_encoding csv hcsv _
    (by exact delayBytes_bytes_length_le csv)
    (by
      intro d hd
      rw [List.mem_reverse] at hd
      exact bytesOf_lt _ d hd) h

/-- **Exact boundary.**  The fixed-width payload round-trips to the nominal
delay exactly on `csv < 32768`. -/
theorem decodeNum_delayBytes_self_iff (csv : Nat) :
    decodeNum ({} : PolicyFlags) (delayBytes csv) 5 = .ok (csv : Int) ↔ csv < 32768 := by
  constructor
  · intro h
    have hr := decodeNum_delayBytes_range ({} : PolicyFlags) csv (csv : Int) h
    omega
  · intro h
    exact decodeNum_delayBytes csv h

/-- The canonical minimal `CScriptNum` encoding of a delay in
`[32768, 65536)` has at least three bytes: the two-byte payload is not just
unfaithful, a faithful encoding cannot fit in two bytes. -/
theorem scriptNumBE_length_ge_three (csv : Nat) (hlo : 32768 ≤ csv)
    (hhi : csv < 65536) : 3 ≤ (scriptNumBE (csv : Int)).length := by
  rcases Nat.lt_or_ge (scriptNumBE (csv : Int)).length 3 with hlt | hge
  · exfalso
    have hlen : (scriptNumBE (csv : Int)).length ≤ 2 := by omega
    have hval : setVchBE (scriptNumBE (csv : Int)) = (csv : Int) :=
      scriptNumBE_value _ (by
        have hc : ((csv : Int)).natAbs = csv := Int.natAbs_natCast csv
        rw [hc]
        exact Nat.lt_of_lt_of_le hhi (by decide : 65536 ≤ 256 ^ 10))
    have hb := (setVchBE_length_le_two_abs _ hlen (scriptNumBE_digits_lt _)).2
    rw [hval] at hb
    omega
  · exact hge

/-- The canonical `encodeScriptNum` of a delay in `[32768, 65536)` is at least
three bytes long. -/
theorem encodeScriptNum_delay_size_ge_three (csv : Nat) (hlo : 32768 ≤ csv)
    (hhi : csv < 65536) : 3 ≤ (encodeScriptNum (csv : Int) false).size := by
  simp only [encodeScriptNum, bytesFromLE_length, List.length_reverse]
  exact scriptNumBE_length_ge_three csv hlo hhi

/-! ## 3. The `u16` field is wider than the faithful payload -/

theorem toUInt8_mod_65536 (csv : Nat) : csv.toUInt8 = (csv % 65536).toUInt8 := by
  simp only [Nat.toUInt8_eq]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  exact (Nat.mod_mod_of_dvd csv (by decide : 256 ∣ 65536)).symm

theorem shiftRight8_mod_65536 (csv : Nat) :
    (csv >>> 8).toUInt8 = ((csv % 65536) >>> 8).toUInt8 := by
  simp only [Nat.toUInt8_eq]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  have h2 : 2 ^ 8 = 256 := by decide
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, h2]
  have h := Nat.mod_mul_right_div_self csv 256 256
  have h' : csv % 65536 / 256 = csv / 256 % 256 := by simpa using h
  have hlt : csv % 65536 / 256 < 256 :=
    Nat.div_lt_of_lt_mul (m := csv % 65536) (n := 256) (k := 256)
      (by have := Nat.mod_lt csv (by decide : 0 < 65536); omega)
  rw [← h', Nat.mod_eq_of_lt hlt]

/-- `delayBytes` carries only the low 16 bits of `csv`. -/
theorem delayBytes_mod (csv : Nat) : delayBytes csv = delayBytes (csv % 65536) := by
  unfold delayBytes toLocalDelayBytes
  rw [toUInt8_mod_65536 csv, shiftRight8_mod_65536 csv]

/-- `delayBytes` is not injective: `0` and `65536` have the same payload. -/
theorem delayBytes_not_injective : ¬ Function.Injective delayBytes := by
  intro hinj
  have h : delayBytes 65536 = delayBytes 0 := by
    simpa using delayBytes_mod 65536
  have h0 : (65536 : Nat) = 0 := hinj h
  omega

/-- Decoding only sees the low 16 bits of the nominal delay. -/
theorem decodeNum_delayBytes_mod (pol : PolicyFlags) (csv : Nat) :
    decodeNum pol (delayBytes csv) 5 = decodeNum pol (delayBytes (csv % 65536)) 5 := by
  rw [delayBytes_mod]

/-! ## 4. The operand disable bit -/

/-- Every decoded delay below `32768` has a clear BIP 68 operand disable bit,
for an arbitrary script number (not only a `Nat` cast). -/
theorem disableBit_of_lt (n : Int) (hn : n < 32768) :
    Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := by
  have ht : Int.toNat n < 2 ^ 31 := by
    by_cases h : n < 0
    · rw [Int.toNat_of_nonpos (by omega : n ≤ 0)]
      decide
    · have h0 : 0 ≤ n := by omega
      rw [Int.toNat_lt h0]
      have h2 : (32768 : Int) < ((2 ^ 31 : Nat) : Int) := by decide
      omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  have hF : SEQUENCE_LOCKTIME_DISABLE_FLAG = 2 ^ 31 := by decide
  rw [hF, Nat.testBit_two_pow]
  by_cases hj : j = 31
  · subst hj
    rw [Nat.testBit_lt_two_pow ht]
    rfl
  · have h31 : ¬ (31 = j) := by omega
    rw [decide_eq_false h31]
    simp

/-- A two-byte payload can never set the operand disable bit. -/
theorem disableBit_setVchBE_two (l : List Nat) (hlen : l.length ≤ 2)
    (hdig : ∀ d ∈ l, d < 256) :
    Int.toNat (setVchBE l) &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 :=
  disableBit_of_lt _ (setVchBE_length_le_two_abs l hlen hdig).2

/-- **Strengthening of wave 7's `disableBit_delay`**: the disable-bit fact holds
for *every* `csv`, not only `csv < 32768`. -/
theorem disableBit_delay_all (csv : Nat) :
    Int.toNat (setVchBE (bytesOf (delayBytes csv)).reverse) &&&
      SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 := by
  apply disableBit_setVchBE_two
  · exact delayBytes_bytes_length_le csv
  · intro d hd
    rw [List.mem_reverse] at hd
    exact bytesOf_lt _ d hd

/-- Whatever a `delayBytes` payload decodes to (if it decodes at all), the
operand disable bit is clear. -/
theorem disableBit_decodeNum_delayBytes (pol : PolicyFlags) (csv : Nat) (n : Int)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n) :
    Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 :=
  disableBit_of_lt n (decodeNum_delayBytes_range pol csv n hdec).2

/-- The BIP 112 “operand disable bit ⇒ `OP_CSV` is a NOP” branch is unreachable
through the fixed-width `delayBytes` payload. -/
theorem opCsv_disable_nop_unreachable (pol : PolicyFlags) (csv : Nat) (n : Int)
    (hdec : decodeNum pol (delayBytes csv) 5 = .ok n) :
    (Int.toNat n &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) ≠ 0 → False := by
  intro h
  exact h (disableBit_decodeNum_delayBytes pol csv n hdec)

/-! ## 5. `checkSequenceDef` on non-positive operands -/

/-- **Sequence check for a non-positive operand.**  A non-positive operand
`toNat`-truncates to `0`, so the BIP 68/112 check reduces to: version at least
2, transaction disable bit clear, and a height-domain transaction sequence.
The comparison against the operand is vacuously satisfied. -/
theorem checkSequenceDef_of_nonpos (env : LocktimeEnv) (n : Int) (hn : n ≤ 0) :
    checkSequenceDef env n = true ↔
      (¬ env.txVersion < 2) ∧
      (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG := by
  have hn0 : n.toNat = 0 := Int.toNat_of_nonpos hn
  have hT : 0 < SEQUENCE_LOCKTIME_TYPE_FLAG := by decide
  have hstep := step_abstract
    (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) 0 hT
  unfold checkSequenceDef
  dsimp only
  rw [hn0]
  simp only [Nat.zero_and]
  rw [hstep]
  by_cases hv : env.txVersion < 2
  · simp [hv]
  · by_cases hd : (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0
    · simp [hv, hd, Nat.zero_le]
    · simp [hv, hd]

/-- The `csv = 32768` boundary case runs the sequence check on `0`. -/
theorem checkSequenceDef_delayBytes_32768 (env : LocktimeEnv) :
    checkSequenceDef env (0 : Int) = true ↔
      (¬ env.txVersion < 2) ∧
      (env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
      (env.txSequence.toNat &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
        SEQUENCE_LOCKTIME_TYPE_FLAG :=
  checkSequenceDef_of_nonpos env 0 (Int.le_refl 0)

/-! ## 6. `OP_CSV` at the boundary -/

/-- `OP_CSV` with CSV enabled and a non-empty stack rejects a negative decoded
operand with `.error .negativeLocktime`, before the disable-bit NOP and before
any transaction-side comparison. -/
theorem dispatchOp_csv_negative (ctx : Ctx) (st : State) (n : Int)
    (hcsv : ctx.flags.csv = true) (hst : 1 ≤ st.stack.length)
    (hdec : decodeNum ctx.pol (topAt st.stack 1) 5 = .ok n) (hn : n < 0) :
    stepBody.dispatchOp ctx { ast := .op ⟨0xb2, by decide⟩, wire := 0xb2, next := 0 }
      0xb2 (st.vf.all id) st = .error .negativeLocktime := by
  have hst' : ¬ st.stack.length < 1 := by omega
  simp [stepBody.dispatchOp, hcsv, hst', hdec, hn]

/-- **The `csv > 32768` branch is not spendable.**  For `32768 < csv < 65536`
the decoded operand is negative, so the delayed branch aborts at `OP_CSV`
regardless of the transaction sequence context. -/
theorem dispatchOp_csv_delayBytes_neg (ctx : Ctx) (st : State) (csv : Nat)
    (hcsv : ctx.flags.csv = true) (hst : 1 ≤ st.stack.length)
    (htop : topAt st.stack 1 = delayBytes csv)
    (hmin : ctx.pol.minimalData = false)
    (hlo : 32768 < csv) (hhi : csv < 65536) :
    stepBody.dispatchOp ctx { ast := .op ⟨0xb2, by decide⟩, wire := 0xb2, next := 0 }
      0xb2 (st.vf.all id) st = .error .negativeLocktime := by
  have hdec : decodeNum ctx.pol (topAt st.stack 1) 5 =
      .ok (-(((csv - 32768 : Nat)) : Int)) := by
    rw [htop]
    exact decodeNum_delayBytes_ge ctx.pol hmin csv (by omega) hhi
  have hpos : 0 < csv - 32768 := by omega
  have hn : -(((csv - 32768 : Nat)) : Int) < 0 := by omega
  exact dispatchOp_csv_negative ctx st _ hcsv hst hdec hn

/-! ## 7. Vendor verdict at `csv = 32768` and necessity of the range hypothesis -/

/-- **Corrected vendor criterion at the boundary.**  At `csv = 32768` the
faithful payload decodes to `0`, so the full vendored P2WSH verdict is `.ok`
exactly when the sequence check accepts `0` and the delayed-key signature
verifies.  This is the wave-7 criterion with the operand replaced by the
*decoded* value. -/
theorem toLocal_delayed_boundary_32768_vendor_iff
    (chk : ScriptChecker) (revocationKey delayedPaymentKey : PubKey)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768)) = program) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ↔
      (checkSequenceDef chk.env (0 : Int) = true ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) :=
  toLocal_delayed_vendor_iff chk revocationKey delayedPaymentKey 32768 sig 0 program
    hr hd hsigsz (by simpa using decodeNum_delayBytes_32768) (by decide)
    (by decide) hps hprog

/-- **The wave-7 range hypothesis is not removable.**  Take the boundary delay
`csv = 32768` and any transaction context whose masked sequence is below
`32768` (for example `txSequence = 0`).  If the delayed-key signature verifies
and `checkSequenceDef` accepts the decoded operand `0`, then the vendored
verdict is `.ok`, while the *nominal* context claim — the RHS of
`toLocal_delayed_sequence_context_refinement` with `csv = 32768` in place of
the decoded operand — is false.  Hence `hcsv : csv < 32768` (equivalently, the
use of the decoded operand) is essential. -/
theorem boundary_nominal_context_fails
    (chk : ScriptChecker) (revocationKey delayedPaymentKey : PubKey)
    (sig : ByteArray) (program : ByteArray)
    (hr : revocationKey.bytes.size = 33) (hd : delayedPaymentKey.bytes.size = 33)
    (hsigsz : sig.size ≤ 520)
    (hps : program.size = 32)
    (hprog : hashSha256
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768)) = program)
    (hseq0 : checkSequenceDef chk.env (0 : Int) = true)
    (hsig : chk.base.checkECDSASignature sig delayedPaymentKey.bytes
      (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768))
      .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true)
    (hmask : (chk.env.txSequence.toNat &&&
        (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < 32768) :
    verifyWitnessProgram 10
      [sig, ByteArray.empty,
        serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768)]
      0 program ({ csv := true } : ScriptFlags) ({} : PolicyFlags) chk false = .ok ∧
    ¬ ((¬ chk.env.txVersion < 2) ∧
        (chk.env.txSequence.toNat &&& SEQUENCE_LOCKTIME_DISABLE_FLAG) = 0 ∧
        (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) <
          SEQUENCE_LOCKTIME_TYPE_FLAG ∧
        (32768 : Nat) ≤ (chk.env.txSequence.toNat &&&
            (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) ∧
        chk.base.checkECDSASignature sig delayedPaymentKey.bytes
          (serializeOpcodes (toLocalOps revocationKey delayedPaymentKey 32768))
          .witnessV0 (default : Bitcoin.Crypto.Seam.ScriptExecutionData) = true) := by
  constructor
  · rw [toLocal_delayed_boundary_32768_vendor_iff chk revocationKey delayedPaymentKey
      sig program hr hd hsigsz hps hprog]
    exact ⟨hseq0, hsig⟩
  · intro h
    omega

/-- Non-vacuity of the arithmetic side of the boundary counterexample: the
default height-domain context (`version = 2`, `sequence = 0`) accepts the
decoded boundary operand `0`, and its masked sequence is below `32768`. -/
theorem boundary_default_context_witness :
    checkSequenceDef ({ txVersion := 2, txLockTime := 0, txSequence := 0 } :
        LocktimeEnv) (0 : Int) = true ∧
      ((({ txVersion := 2, txLockTime := 0, txSequence := 0 } : LocktimeEnv)).txSequence.toNat
        &&& (SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK)) < 32768 := by
  constructor <;> decide

end LnLean.Proofs.WaveH.H06
