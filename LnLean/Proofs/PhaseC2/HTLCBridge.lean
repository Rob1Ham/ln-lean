import LnLean

/-!
# LnLean.Proofs.PhaseC2.HTLCBridge

**English claim.**  A BOLT 3 HTLC output has two script paths.  The
payment-hash path is opened by a 32-byte preimage whose hash equals the
payment hash committed to by the output, together with the recipient's
signature.  The timeout path becomes available at or after the committed
`cltv_expiry` and is authorised by the sender's signature.

This module builds an explicit two-branch witness-script template, proves:

* both branches are nonempty and the enclosing output has BIP 141 P2WSH
  shape;
* the branches carry an explicit structural tag, so a payment branch is
  never the same byte string as a timeout branch;
* a conditional spendability composition through an explicit
  `HTLCSpendBridge` structure whose soundness/completeness fields are
  hypotheses, never axioms.

The L1 script interpreter, `OP_IF` selection, `OP_HASH160`, `OP_CLTV`, and
BIP 143 signature checking are deliberately abstracted by the fields of
`HTLCSpendBridge` (obligation `PC2-HTLC-001`).  No placeholder proofs and no
axioms occur in this module, and `vendor/` is not touched.

**BOLT sections.**  BOLT 3 §Offered/Received HTLC Outputs; BOLT 2
§Adding/Removing an HTLC.
-/

namespace LnLean.Proofs.PhaseC2.HTLCBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LnLean LnLean.Bitcoin LnLean.Crypto

/-! ## The two branch templates -/

/-- The payment-hash (success) branch:
`OP_HASH160 <payment_hash> OP_EQUALVERIFY <recipient_key> OP_CHECKSIG`.
The `OP_HASH160` marker stands for the hash lock; the concrete SHA-256 opcode
is outside the wave-A opcode subset. -/
def paymentBranchScript (paymentHash : PaymentHash) (recipientKey : PubKey) :
    Script :=
  ⟨(ByteArray.empty.push OP_HASH160)
     ++ pushData paymentHash.bytes
     ++ (ByteArray.empty.push OP_EQUALVERIFY)
     ++ pushData recipientKey.bytes
     ++ (ByteArray.empty.push OP_CHECKSIG)⟩

/-- The timeout branch:
`<cltv_expiry> OP_CLTV OP_DROP <sender_key> OP_CHECKSIG`.

The expiry uses phase C's fixed-width four-byte `pushScriptNum32`; for all
BOLT 2 expiries (`< 500000000 < 2^32`) this encoding is injective. -/
def timeoutBranchScript (cltvExpiry : Height) (senderKey : PubKey) : Script :=
  ⟨pushScriptNum32 cltvExpiry
     ++ (ByteArray.empty.push OP_CLTV)
     ++ (ByteArray.empty.push OP_DROP)
     ++ pushData senderKey.bytes
     ++ (ByteArray.empty.push OP_CHECKSIG)⟩

/-- The two-branch HTLC witness script:
`OP_IF <success branch> OP_ELSE <timeout branch> OP_ENDIF`. -/
def twoBranchScript (paymentHash : PaymentHash) (cltvExpiry : Height)
    (recipientKey senderKey : PubKey) : Script :=
  ⟨(ByteArray.empty.push OP_IF)
     ++ (paymentBranchScript paymentHash recipientKey).bytes
     ++ (ByteArray.empty.push OP_ELSE)
     ++ (timeoutBranchScript cltvExpiry senderKey).bytes
     ++ (ByteArray.empty.push OP_ENDIF)⟩

/-- The P2WSH output script committing to the two-branch witness script.
The concrete hash is a parameter, as in the seam. -/
def htlcScriptPubKey (sha256 : ByteArray → ByteArray) (paymentHash : PaymentHash)
    (cltvExpiry : Height) (recipientKey senderKey : PubKey) : Script :=
  p2wsh (sha256 (twoBranchScript paymentHash cltvExpiry recipientKey senderKey).bytes)

/-! ## Nonemptiness and P2WSH shape -/

theorem paymentBranch_nonempty (ph : PaymentHash) (key : PubKey) :
    (paymentBranchScript ph key).bytes.size > 0 := by
  simp [paymentBranchScript]

theorem timeoutBranch_nonempty (cltv : Height) (key : PubKey) :
    (timeoutBranchScript cltv key).bytes.size > 0 := by
  simp [timeoutBranchScript]

theorem twoBranchScript_nonempty (ph : PaymentHash) (cltv : Height)
    (recipientKey senderKey : PubKey) :
    (twoBranchScript ph cltv recipientKey senderKey).bytes.size > 0 := by
  simp [twoBranchScript, paymentBranchScript, timeoutBranchScript]

/-- The HTLC output is exactly the BIP 141 P2WSH commitment to the
two-branch witness script. -/
theorem htlcScriptPubKey_eq_p2wsh (sha256 : ByteArray → ByteArray)
    (ph : PaymentHash) (cltv : Height) (recipientKey senderKey : PubKey) :
    htlcScriptPubKey sha256 ph cltv recipientKey senderKey =
      p2wsh (sha256 (twoBranchScript ph cltv recipientKey senderKey).bytes) := rfl

/-- The raw P2WSH output is `OP_0 <0x20> <witness-script-hash>`. -/
theorem htlcScriptPubKey_bytes (sha256 : ByteArray → ByteArray)
    (ph : PaymentHash) (cltv : Height) (recipientKey senderKey : PubKey) :
    (htlcScriptPubKey sha256 ph cltv recipientKey senderKey).bytes =
      (ByteArray.empty.push OP_0).push 0x20 ++
        sha256 (twoBranchScript ph cltv recipientKey senderKey).bytes := rfl

/-- A 32-byte witness-script hash yields a 34-byte P2WSH output script. -/
theorem htlcScriptPubKey_p2wsh_shape (sha256 : ByteArray → ByteArray)
    (ph : PaymentHash) (cltv : Height) (recipientKey senderKey : PubKey)
    (h : (sha256 (twoBranchScript ph cltv recipientKey senderKey).bytes).size = 32) :
    (htlcScriptPubKey sha256 ph cltv recipientKey senderKey).bytes.size = 34 := by
  simpa [htlcScriptPubKey] using
    LnLean.Bitcoin.p2wsh_size
      (sha256 (twoBranchScript ph cltv recipientKey senderKey).bytes) h

/-! ## Structural branch tags -/

/-- The two branches of the HTLC template. -/
inductive HtlcBranchTag where
  | payment
  | timeout
deriving DecidableEq, Repr

/-- Read the branch tag from the first script byte.  A payment branch starts
with `OP_HASH160` (`0xa9`); a timeout branch starts with the length byte `4`
of the fixed-width `pushScriptNum32`.  These tags are structural and do not
depend on any cryptographic assumption. -/
def branchTag (s : Script) : Option HtlcBranchTag :=
  if s.bytes[0]? = some OP_HASH160 then some .payment
  else if s.bytes[0]? = some (4 : UInt8) then some .timeout
  else none

private theorem firstByte_empty_push (a : UInt8) (x : ByteArray) :
    ((ByteArray.empty.push a) ++ x)[0]! = a := by
  have hs : 0 < ((ByteArray.empty.push a) ++ x).size := by
    simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty]
    omega
  rw [getElem!_pos (ByteArray.empty.push a ++ x) 0 hs]
  rw [ByteArray.getElem_append_left (i := 0) (by
    simp only [ByteArray.size_push, ByteArray.size_empty]
    omega)]
  simpa using ByteArray.getElem!_push_eq ByteArray.empty a

private theorem firstByte?_empty_push (a : UInt8) (x : ByteArray) :
    ((ByteArray.empty.push a) ++ x)[0]? = some a := by
  rw [getElem?_eq_some_iff]
  refine ⟨?_, firstByte_empty_push a x⟩
  simp only [ByteArray.size_append, ByteArray.size_push, ByteArray.size_empty]
  omega

private theorem pushUInt32LE_size_local (n : Nat) : (pushUInt32LE n).size = 4 := by
  unfold pushUInt32LE
  simp only [ByteArray.size_push, ByteArray.size_empty]

private theorem firstByte?_pushScriptNum32 (c : Height) (x : ByteArray) :
    (pushScriptNum32 c ++ x)[0]? = some (4 : UInt8) := by
  have hs : (pushUInt32LE c).size = 4 := pushUInt32LE_size_local c
  rw [pushScriptNum32, pushData, hs]
  rw [ByteArray.append_assoc]
  exact firstByte?_empty_push (4 : UInt8) (pushUInt32LE c ++ x)

theorem paymentBranch_byte? (ph : PaymentHash) (key : PubKey) :
    (paymentBranchScript ph key).bytes[0]? = some OP_HASH160 := by
  unfold paymentBranchScript
  simpa only [ByteArray.append_assoc] using
    firstByte?_empty_push OP_HASH160
      (pushData ph.bytes ++ (ByteArray.empty.push OP_EQUALVERIFY)
        ++ pushData key.bytes ++ (ByteArray.empty.push OP_CHECKSIG))

theorem timeoutBranch_byte? (cltv : Height) (key : PubKey) :
    (timeoutBranchScript cltv key).bytes[0]? = some (4 : UInt8) := by
  unfold timeoutBranchScript
  simpa only [ByteArray.append_assoc] using
    firstByte?_pushScriptNum32 cltv
      ((ByteArray.empty.push OP_CLTV) ++ (ByteArray.empty.push OP_DROP)
        ++ pushData key.bytes ++ (ByteArray.empty.push OP_CHECKSIG))

theorem paymentBranch_tag (ph : PaymentHash) (key : PubKey) :
    branchTag (paymentBranchScript ph key) = some .payment := by
  unfold branchTag
  rw [ite_eq_left (paymentBranch_byte? ph key)]

theorem timeoutBranch_tag (cltv : Height) (key : PubKey) :
    branchTag (timeoutBranchScript cltv key) = some .timeout := by
  have h0 := timeoutBranch_byte? cltv key
  have hne : (timeoutBranchScript cltv key).bytes[0]? ≠ some OP_HASH160 := by
    rw [h0]
    decide
  unfold branchTag
  rw [ite_eq_right hne, ite_eq_left h0]

/-- **Branch distinguishability.**  The payment-hash branch and the timeout
branch are different byte strings for every choice of parameters.  The proof
uses only the structural tags above. -/
theorem paymentBranch_ne_timeoutBranch (ph : PaymentHash) (cltv : Height)
    (recipientKey senderKey : PubKey) :
    paymentBranchScript ph recipientKey ≠ timeoutBranchScript cltv senderKey := by
  intro h
  have ht := paymentBranch_tag ph recipientKey
  rw [h, timeoutBranch_tag] at ht
  have hne : HtlcBranchTag.timeout ≠ HtlcBranchTag.payment := by decide
  exact hne (Option.some.inj ht)

/-- The two branches also carry distinct tags even when only the tag map is
observed. -/
theorem payment_timeout_tags_distinct (ph : PaymentHash) (cltv : Height)
    (recipientKey senderKey : PubKey) :
    branchTag (paymentBranchScript ph recipientKey) ≠
      branchTag (timeoutBranchScript cltv senderKey) := by
  rw [paymentBranch_tag, timeoutBranch_tag]
  decide

/-! ## The abstract L1 spend bridge (obligation PC2-HTLC-001) -/

/-- Which branch of the HTLC script is selected. -/
inductive HtlcPath where
  | payment
  | timeout
deriving Repr, DecidableEq, BEq

/-- The data committed to by one HTLC output. -/
structure HtlcTerms where
  paymentHash : PaymentHash
  cltvExpiry : Height
  recipientKey : PubKey
  senderKey : PubKey
deriving Repr

namespace HtlcTerms

/-- The two-branch witness script of these terms. -/
def witnessScript (t : HtlcTerms) : Script :=
  twoBranchScript t.paymentHash t.cltvExpiry t.recipientKey t.senderKey

/-- The P2WSH output script, parameterised by the concrete hash. -/
def scriptPubKey (sha256 : ByteArray → ByteArray) (t : HtlcTerms) : Script :=
  htlcScriptPubKey sha256 t.paymentHash t.cltvExpiry t.recipientKey t.senderKey

end HtlcTerms

/-- The two path conditions, stated independently of the interpreter. -/
def PaymentEnabled (sha256 : ByteArray → ByteArray) (t : HtlcTerms)
    (p : Preimage) : Prop :=
  p.Valid ∧ sha256 p.bytes = t.paymentHash.bytes

/-- The timeout path is enabled at `height` exactly when the committed CLTV
expiry has been reached. -/
def TimeoutEnabled (t : HtlcTerms) (height : Height) : Prop :=
  t.cltvExpiry ≤ height

/-- **The L1 spend bridge.**  `spend t path key witness tx` means that the L1
interpreter accepts `witness` for the P2WSH output of `t` on transaction
`tx`, choosing `path`, with `key` as the authorised signing key.

The four `Prop` fields are the **L1 interpreter obligation**
`PC2-HTLC-001`: they connect `spend` to `Bitcoin.Data.Script` execution,
including the `OP_IF` selector, the `OP_HASH160`/preimage check, `OP_CLTV`
against `tx.locktime`, and BIP 143 `OP_CHECKSIG`.  They are structure fields
(hypotheses of every composition below), never axioms of this module. -/
-- OBLIGATION: PC2-HTLC-001 L1 Script interpreter for the HTLC branches.
structure HTLCSpendBridge (sha256 : ByteArray → ByteArray) where
  spend : HtlcTerms → HtlcPath → PubKey → WitnessStack → Tx → Prop
  /-- Soundness of the payment-hash branch: a successful spend reveals a
  valid 32-byte preimage hashing to the committed payment hash and is
  authorised by the committed recipient key. -/
  payment_sound : ∀ (t : HtlcTerms) (key : PubKey) (w : WitnessStack) (tx : Tx),
    spend t .payment key w tx →
      ∃ p : Preimage, p.Valid ∧ sha256 p.bytes = t.paymentHash.bytes ∧
        key = t.recipientKey
  /-- Soundness of the timeout branch: a successful spend has
  `cltv_expiry ≤ tx.locktime` and is authorised by the committed sender key. -/
  timeout_sound : ∀ (t : HtlcTerms) (key : PubKey) (w : WitnessStack) (tx : Tx),
    spend t .timeout key w tx →
      t.cltvExpiry ≤ tx.locktime.toNat ∧ key = t.senderKey
  /-- Completeness of the payment-hash branch: every valid matching preimage
  can be used with the recipient key. -/
  payment_complete : ∀ (t : HtlcTerms) (p : Preimage),
    p.Valid → sha256 p.bytes = t.paymentHash.bytes →
      ∃ (w : WitnessStack) (tx : Tx), spend t .payment t.recipientKey w tx
  /-- Completeness of the timeout branch: at or after the expiry, the sender
  key can spend with a transaction whose locktime is that height. -/
  timeout_complete : ∀ (t : HtlcTerms) (height : Height),
    t.cltvExpiry ≤ height →
      ∃ (w : WitnessStack) (tx : Tx),
        tx.locktime.toNat = height ∧ spend t .timeout t.senderKey w tx

/-! ## Conditional spendability and soundness -/

/-- A valid matching preimage makes the payment path spendable. -/
theorem payment_path_spendable (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (p : Preimage)
    (hp : PaymentEnabled sha256 t p) :
    ∃ (w : WitnessStack) (tx : Tx), B.spend t .payment t.recipientKey w tx :=
  B.payment_complete t p hp.1 hp.2

/-- A successful payment spend reveals a matching preimage. -/
theorem payment_spend_reveals_matching_preimage (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .payment key w tx) :
    ∃ p : Preimage, PaymentEnabled sha256 t p := by
  rcases B.payment_sound t key w tx h with ⟨p, hpv, hph, _⟩
  exact ⟨p, hpv, hph⟩

/-- A successful payment spend is authorised by the recipient key. -/
theorem payment_spend_authorized_by_recipient (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .payment key w tx) :
    key = t.recipientKey := by
  rcases B.payment_sound t key w tx h with ⟨p, hpv, hph, hk⟩
  exact hk

/-- Combined payment-path soundness. -/
theorem payment_spend_sound (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .payment key w tx) :
    (∃ p : Preimage, PaymentEnabled sha256 t p) ∧ key = t.recipientKey :=
  ⟨payment_spend_reveals_matching_preimage sha256 B h,
    payment_spend_authorized_by_recipient sha256 B h⟩

/-- At or after the committed expiry the timeout path is spendable by the
sender, with the transaction locktime equal to the chosen height. -/
theorem timeout_path_spendable (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (height : Height)
    (hh : TimeoutEnabled t height) :
    ∃ (w : WitnessStack) (tx : Tx),
      tx.locktime.toNat = height ∧ B.spend t .timeout t.senderKey w tx :=
  B.timeout_complete t height hh

/-- A successful timeout spend happens at or after the committed expiry. -/
theorem timeout_spend_after_expiry (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .timeout key w tx) :
    t.cltvExpiry ≤ tx.locktime.toNat :=
  (B.timeout_sound t key w tx h).1

/-- A successful timeout spend is authorised by the sender key. -/
theorem timeout_spend_authorized_by_sender (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .timeout key w tx) :
    key = t.senderKey :=
  (B.timeout_sound t key w tx h).2

/-- Combined timeout-path soundness. -/
theorem timeout_spend_sound (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) {t : HtlcTerms} {key : PubKey}
    {w : WitnessStack} {tx : Tx} (h : B.spend t .timeout key w tx) :
    t.cltvExpiry ≤ tx.locktime.toNat ∧ key = t.senderKey :=
  B.timeout_sound t key w tx h

/-- **Conditional spendability composition.**  Given both path conditions,
the bridge yields a payment spend and a timeout spend (the latter with the
requested locktime).  This is the composed statement: it inherits exactly
the four fields of `HTLCSpendBridge`, so it never asserts the missing L1
interpreter facts unconditionally. -/
theorem htlc_spendability_composition (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (p : Preimage) (height : Height)
    (hp : PaymentEnabled sha256 t p) (ht : TimeoutEnabled t height) :
    (∃ (w : WitnessStack) (tx : Tx), B.spend t .payment t.recipientKey w tx) ∧
    (∃ (w : WitnessStack) (tx : Tx),
      tx.locktime.toNat = height ∧ B.spend t .timeout t.senderKey w tx) :=
  ⟨payment_path_spendable sha256 B t p hp,
    timeout_path_spendable sha256 B t height ht⟩

/-! ## Disjointness -/

/-- **Authority disjointness.**  When the recipient and sender keys differ, a
single key cannot authorise both branches of the same HTLC output. -/
theorem branches_not_both_authorized_by_one_key (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (key : PubKey)
    (w : WitnessStack) (tx : Tx) (hneq : t.recipientKey ≠ t.senderKey) :
    ¬ (B.spend t .payment key w tx ∧ B.spend t .timeout key w tx) := by
  rintro ⟨hp, ht⟩
  have hp' := payment_spend_authorized_by_recipient sha256 B hp
  have ht' := timeout_spend_authorized_by_sender sha256 B ht
  exact hneq (hp'.symm.trans ht')

/-- The recipient key cannot authorise the timeout branch. -/
theorem timeout_not_authorized_by_recipient (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (w : WitnessStack) (tx : Tx)
    (hneq : t.senderKey ≠ t.recipientKey) :
    ¬ B.spend t .timeout t.recipientKey w tx := by
  intro h
  exact hneq ((timeout_spend_authorized_by_sender sha256 B h).symm)

/-- The sender key cannot authorise the payment branch. -/
theorem payment_not_authorized_by_sender (sha256 : ByteArray → ByteArray)
    (B : HTLCSpendBridge sha256) (t : HtlcTerms) (w : WitnessStack) (tx : Tx)
    (hneq : t.recipientKey ≠ t.senderKey) :
    ¬ B.spend t .payment t.senderKey w tx := by
  intro h
  exact hneq (payment_spend_authorized_by_recipient sha256 B h).symm

/-- **Preimage uniqueness under explicit hash binding.**  Under collision
resistance, a payment hash has at most one valid preimage. -/
theorem payment_preimage_unique {sha256 : ByteArray → ByteArray}
    (hcr : CollisionResistant sha256) {t : HtlcTerms} {p q : Preimage}
    (hp : PaymentEnabled sha256 t p) (hq : PaymentEnabled sha256 t q) : p = q := by
  have hd : sha256 p.bytes = sha256 q.bytes := by
    rw [hp.2, hq.2]
  have hb : p.bytes = q.bytes := hcr p.bytes q.bytes hp.1 hq.1 hd
  cases p
  cases q
  simp_all

/-- One preimage cannot satisfy two outputs with distinct payment hashes.
Both hashes are the digest of the same preimage, so the binding is
unconditional here; collision resistance is needed only for preimage
uniqueness (`payment_preimage_unique`). -/
theorem payment_branches_disjoint_of_hash_ne {sha256 : ByteArray → ByteArray}
    {t₁ t₂ : HtlcTerms} {p : Preimage}
    (h₁ : PaymentEnabled sha256 t₁ p) (h₂ : PaymentEnabled sha256 t₂ p)
    (hne : t₁.paymentHash ≠ t₂.paymentHash) : False := by
  apply hne
  have hbytes : t₁.paymentHash.bytes = t₂.paymentHash.bytes := by
    rw [← h₁.2, h₂.2]
  cases hph₁ : t₁.paymentHash
  cases hph₂ : t₂.paymentHash
  simp_all

/-- **Temporal separation.**  Before the committed expiry the timeout branch
is not enabled; the payment branch may still be enabled. -/
theorem timeout_not_enabled_before_expiry (t : HtlcTerms) (height : Height)
    (h : height < t.cltvExpiry) : ¬ TimeoutEnabled t height := by
  intro he
  exact Nat.not_le.mpr h he

/-! ## Injectivity of the branch encodings

The payment-hash branch commits to `sha256(preimage)` and to the recipient
key; the timeout branch commits to a fixed-width four-byte CLTV expiry and to
the sender key.  Distinct parameters therefore give distinct witness scripts.
These are the phase-C encoding facts that justify treating a branch as a
commitment rather than an unstructured byte blob. -/

/-- `pushData` is injective: its single length-prefix byte can be cancelled.
This is a local copy of the private lemma in
`LnLean.Proofs.Bitcoin.ScriptProps`; it is re-proved here so the bridge does
not depend on a private name. -/
private theorem pushData_injective_local {a b : ByteArray}
    (h : pushData a = pushData b) : a = b := by
  unfold pushData at h
  exact ((ByteArray.append_eq_append_iff_of_size_eq_left (by simp)).mp h).2

/-- Distinct payment hashes, with the recipient key fixed, give distinct
payment-branch scripts.  The extraction cancels the common `OP_HASH160`
prefix and the common suffix ending in `OP_CHECKSIG`. -/
theorem paymentBranch_paymentHash_injective (ph₁ ph₂ : PaymentHash)
    (recipientKey : PubKey)
    (h : paymentBranchScript ph₁ recipientKey =
      paymentBranchScript ph₂ recipientKey) : ph₁ = ph₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushData ph₁.bytes = pushData ph₂.bytes := by
    simpa only [paymentBranchScript, ByteArray.append_assoc,
      ByteArray.append_right_inj, ByteArray.append_left_inj] using hb
  have hbytes := pushData_injective_local hX
  cases ph₁
  cases ph₂
  simpa using hbytes

/-- Distinct recipient keys, with the payment hash fixed, give distinct
payment-branch scripts. -/
theorem paymentBranch_recipientKey_injective (ph : PaymentHash)
    (recipientKey₁ recipientKey₂ : PubKey)
    (h : paymentBranchScript ph recipientKey₁ =
      paymentBranchScript ph recipientKey₂) : recipientKey₁ = recipientKey₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushData recipientKey₁.bytes = pushData recipientKey₂.bytes := by
    simpa only [paymentBranchScript, ByteArray.append_assoc,
      ByteArray.append_right_inj, ByteArray.append_left_inj] using hb
  have hbytes := pushData_injective_local hX
  cases recipientKey₁
  cases recipientKey₂
  simpa using hbytes

/-- Distinct four-byte-encodable CLTV expiries, with the sender key fixed,
give distinct timeout-branch scripts.  The bound `< 2^32` is exactly the
range in which `pushScriptNum32` is injective. -/
theorem timeoutBranch_cltv_injective (cltv₁ cltv₂ : Height) (senderKey : PubKey)
    (h₁ : cltv₁ < 2^32) (h₂ : cltv₂ < 2^32)
    (h : timeoutBranchScript cltv₁ senderKey =
      timeoutBranchScript cltv₂ senderKey) : cltv₁ = cltv₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushScriptNum32 cltv₁ = pushScriptNum32 cltv₂ := by
    simpa only [timeoutBranchScript, ByteArray.append_assoc,
      ByteArray.append_left_inj] using hb
  exact LnLean.Proofs.Bitcoin.ScriptProps.pushScriptNum32_injective h₁ h₂ hX

/-- Distinct sender keys, with the CLTV expiry fixed, give distinct
timeout-branch scripts. -/
theorem timeoutBranch_senderKey_injective (cltv : Height)
    (senderKey₁ senderKey₂ : PubKey)
    (h : timeoutBranchScript cltv senderKey₁ =
      timeoutBranchScript cltv senderKey₂) : senderKey₁ = senderKey₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushData senderKey₁.bytes = pushData senderKey₂.bytes := by
    simpa only [timeoutBranchScript, ByteArray.append_assoc,
      ByteArray.append_right_inj, ByteArray.append_left_inj] using hb
  have hbytes := pushData_injective_local hX
  cases senderKey₁
  cases senderKey₂
  simpa using hbytes

/-- The enclosing two-branch script inherits payment-hash injectivity. -/
theorem twoBranch_paymentHash_injective (ph₁ ph₂ : PaymentHash)
    (cltvExpiry : Height) (recipientKey senderKey : PubKey)
    (h : twoBranchScript ph₁ cltvExpiry recipientKey senderKey =
      twoBranchScript ph₂ cltvExpiry recipientKey senderKey) : ph₁ = ph₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushData ph₁.bytes = pushData ph₂.bytes := by
    simpa only [twoBranchScript, paymentBranchScript, timeoutBranchScript,
      ByteArray.append_assoc, ByteArray.append_right_inj,
      ByteArray.append_left_inj] using hb
  have hbytes := pushData_injective_local hX
  cases ph₁
  cases ph₂
  simpa using hbytes

/-- The enclosing two-branch script inherits CLTV injectivity. -/
theorem twoBranch_cltv_injective (ph : PaymentHash) (cltv₁ cltv₂ : Height)
    (recipientKey senderKey : PubKey)
    (h₁ : cltv₁ < 2^32) (h₂ : cltv₂ < 2^32)
    (h : twoBranchScript ph cltv₁ recipientKey senderKey =
      twoBranchScript ph cltv₂ recipientKey senderKey) : cltv₁ = cltv₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  have hX : pushScriptNum32 cltv₁ = pushScriptNum32 cltv₂ := by
    simpa only [twoBranchScript, paymentBranchScript, timeoutBranchScript,
      ByteArray.append_assoc, ByteArray.append_right_inj,
      ByteArray.append_left_inj] using hb
  exact LnLean.Proofs.Bitcoin.ScriptProps.pushScriptNum32_injective h₁ h₂ hX

/-- Phase-C reuse: the BOLT 3 offered-HTLC witness script is injective in its
20-byte payment-hash digest. -/
theorem bolt3_offeredHtlc_paymentHash_injective
    (revocationKeyHash160 : ByteArray) (remoteHtlcKey localHtlcKey : PubKey)
    {h₁ h₂ : ByteArray} (hh₁ : h₁.size = 20) (hh₂ : h₂.size = 20)
    (h : offeredHtlcWitnessScript revocationKeyHash160 h₁ remoteHtlcKey localHtlcKey =
      offeredHtlcWitnessScript revocationKeyHash160 h₂ remoteHtlcKey localHtlcKey) :
    h₁ = h₂ :=
  LnLean.Proofs.Bitcoin.ScriptProps.offeredHtlcWitnessScript_paymentHash_injective
    revocationKeyHash160 remoteHtlcKey localHtlcKey hh₁ hh₂ h

/-- Phase-C reuse: the BOLT 3 received-HTLC witness script is injective in
its four-byte CLTV expiry, for all expiries below `2^32`. -/
theorem bolt3_receivedHtlc_cltv_injective
    (revocationKeyHash160 paymentHash160 : ByteArray)
    (remoteHtlcKey localHtlcKey : PubKey) {c₁ c₂ : Height}
    (h₁ : c₁ < 2^32) (h₂ : c₂ < 2^32)
    (h : receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c₁ =
        receivedHtlcWitnessScript revocationKeyHash160 paymentHash160
          remoteHtlcKey localHtlcKey c₂) : c₁ = c₂ :=
  LnLean.Proofs.Bitcoin.ScriptProps.receivedHtlcWitnessScript_cltv_injective
    revocationKeyHash160 paymentHash160 remoteHtlcKey localHtlcKey h₁ h₂ h

/-! ## The wave-A seam template

`LnLean.Bitcoin.htlcBranchScript` is a one-byte-CLTV scaffold marker.  It is
still useful for traceability, but its CLTV encoding is only injective below
`256`; above that, the `toUInt8` truncation identifies distinct expiries.  The
counterexample below records that gap rather than hiding it. -/

/-- Byte decomposition of the wave-A seam template, isolating the payment-hash
push and the one-byte CLTV push. -/
private theorem seamBranch_decompose (ph : PaymentHash) (cltv : Height)
    (pk : PubKey) :
    (htlcBranchScript ph cltv pk).bytes =
      ((ByteArray.empty.push OP_IF)
        ++ ((ByteArray.empty.push OP_HASH160).push 0x14))
      ++ pushData ph.bytes
      ++ ((ByteArray.empty.push OP_EQUALVERIFY)
        ++ pushData (ByteArray.mk #[cltv.toUInt8])
        ++ ((ByteArray.empty.push OP_CLTV).push OP_DROP)
        ++ pushData pk.bytes
        ++ (ByteArray.empty.push OP_CHECKSIG)
        ++ (ByteArray.empty.push OP_ELSE)
        ++ (ByteArray.empty.push OP_ENDIF)) := by
  unfold htlcBranchScript
  simp only [ByteArray.append_assoc]

/-- The seam template is injective in the payment hash. -/
theorem seamBranch_paymentHash_injective (ph₁ ph₂ : PaymentHash)
    (cltv : Height) (pk : PubKey)
    (h : htlcBranchScript ph₁ cltv pk = htlcBranchScript ph₂ cltv pk) :
    ph₁ = ph₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  rw [seamBranch_decompose ph₁ cltv pk, seamBranch_decompose ph₂ cltv pk] at hb
  have hX : pushData ph₁.bytes = pushData ph₂.bytes := by
    simpa only [ByteArray.append_assoc, ByteArray.append_right_inj,
      ByteArray.append_left_inj] using hb
  have hbytes := pushData_injective_local hX
  cases ph₁
  cases ph₂
  simpa using hbytes

/-- The seam template is injective in the CLTV expiry only on `[0, 256)`. -/
theorem seamBranch_cltv_injective_of_lt_256 (ph : PaymentHash) (pk : PubKey)
    {c₁ c₂ : Height} (h₁ : c₁ < 256) (h₂ : c₂ < 256)
    (h : htlcBranchScript ph c₁ pk = htlcBranchScript ph c₂ pk) : c₁ = c₂ := by
  have hb := congrArg (fun s : Script => s.bytes) h
  rw [seamBranch_decompose ph c₁ pk, seamBranch_decompose ph c₂ pk] at hb
  have hX : pushData (ByteArray.mk #[c₁.toUInt8]) =
      pushData (ByteArray.mk #[c₂.toUInt8]) := by
    simpa only [ByteArray.append_assoc, ByteArray.append_right_inj,
      ByteArray.append_left_inj] using hb
  have hbc := pushData_injective_local hX
  have h0 : (ByteArray.mk #[c₁.toUInt8])[0]! =
      (ByteArray.mk #[c₂.toUInt8])[0]! := by
    rw [hbc]
  have hn : c₁.toUInt8.toNat = c₂.toUInt8.toNat := congrArg UInt8.toNat h0
  have hm : c₁ % 256 = c₂ % 256 := by
    simpa [Nat.toUInt8_eq, UInt8.toNat_ofNat'] using hn
  have hc₁ : c₁ % 256 = c₁ := Nat.mod_eq_of_lt h₁
  have hc₂ : c₂ % 256 = c₂ := Nat.mod_eq_of_lt h₂
  exact hc₁.symm.trans (hm.trans hc₂)

/-- **Seam gap, checked.**  Expiries `0` and `256` produce the same wave-A
seam script, because both truncate to the same `UInt8`. -/
theorem seamBranch_cltv_collision :
    htlcBranchScript ⟨ByteArray.empty⟩ 0 ⟨ByteArray.empty⟩ =
      htlcBranchScript ⟨ByteArray.empty⟩ 256 ⟨ByteArray.empty⟩ := by
  rfl

/-- Consequently the seam template's CLTV encoding is not injective without a
range restriction. -/
theorem seamBranch_cltv_not_injective_unbounded :
    ¬ (∀ (c₁ c₂ : Height),
        htlcBranchScript ⟨ByteArray.empty⟩ c₁ ⟨ByteArray.empty⟩ =
          htlcBranchScript ⟨ByteArray.empty⟩ c₂ ⟨ByteArray.empty⟩ → c₁ = c₂) := by
  intro hinj
  have h := hinj 0 256 seamBranch_cltv_collision
  exact (by decide : (0 : Height) ≠ 256) h

/-- An accepted BOLT 2 HTLC has an expiry below `2^32`, so the four-byte
encoding used by the two-branch template is lossless on real channel states. -/
theorem addHTLC_cltv_lt_two_pow_32
    (maxHtlcValue currentTotal : Msat) (id : Nat) (dir : Direction)
    (amount : Msat) (ph : PaymentHash) (cltv : Height)
    (h : LnLean.Channel.HTLCRecord)
    (ok : LnLean.Channel.addHTLC maxHtlcValue currentTotal id dir amount ph cltv =
      .ok h) :
    h.cltvExpiry < 2^32 := by
  have hmax :=
    LnLean.Proofs.Channel.HTLCProps.add_cltv_lt_model_max
      maxHtlcValue currentTotal id dir amount ph cltv h ok
  have hM : LnLean.Channel.MAX_CLTV_EXPIRY = 500000000 := rfl
  rw [hM] at hmax
  exact Nat.lt_trans hmax (by decide)

/-! ## Cryptographic consequences -/

/-- A hash collision is exactly two distinct valid preimages with the same
digest; this is the general form used below. -/
theorem payment_preimage_unique_of_hash_eq {sha256 : ByteArray → ByteArray}
    (hcr : CollisionResistant sha256) {p q : Preimage}
    (hp : p.Valid) (hq : q.Valid) (h : sha256 p.bytes = sha256 q.bytes) :
    p = q := by
  have hb := hcr p.bytes q.bytes hp hq h
  cases p
  cases q
  simpa using hb

/-- Two distinct preimages cannot both open the same payment hash. -/
theorem payment_branches_disjoint_of_preimage_ne
    {sha256 : ByteArray → ByteArray} (hcr : CollisionResistant sha256)
    {t : HtlcTerms} {p q : Preimage}
    (hp : PaymentEnabled sha256 t p) (hq : PaymentEnabled sha256 t q)
    (hne : p ≠ q) : False :=
  hne (payment_preimage_unique hcr hp hq)

/-- A successful payment spend reveals a preimage that is unique under
collision resistance. -/
theorem payment_spend_reveals_unique_preimage (sha256 : ByteArray → ByteArray)
    (hcr : CollisionResistant sha256) (B : HTLCSpendBridge sha256)
    {t : HtlcTerms} {key : PubKey} {w : WitnessStack} {tx : Tx}
    (h : B.spend t .payment key w tx) :
    ∃ p : Preimage, PaymentEnabled sha256 t p ∧
      ∀ q : Preimage, PaymentEnabled sha256 t q → q = p := by
  obtain ⟨p, hp⟩ := payment_spend_reveals_matching_preimage sha256 B h
  exact ⟨p, hp, fun q hq => payment_preimage_unique hcr hq hp⟩

end LnLean.Proofs.PhaseC2.HTLCBridge
